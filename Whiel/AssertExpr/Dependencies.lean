-- Author: Jesse Comer
import Databases.RelCalc.Dependencies
import Databases.RelCalc.FormulaSemantics
import Databases.Datalog.RAConsequence
import Whiel.AssertExpr.Semantics
import Whiel.Guard.Syntax
import Whiel.Rewrites.UnnamedRA

/-
  This file compiles strict RelCalc TGDs and EGDs to Whiel
  assertions.

  TGD and EGD compilation are exposed separately. The
  relational conjunction compiler reuses the checked
  Datalog SPJ body translation.
-/

------------------------------------------------------------
-- Dependency Views
------------------------------------------------------------

namespace RelCalc

namespace Dependency

namespace Compile

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Stripping universal quantifiers is reversible. -/
theorem forallMany_stripForalls
    (φ : Formula D Γ) :
    Formula.forallMany (Formula.stripForalls φ).1
        (Formula.stripForalls φ).2 = φ := by
  induction φ with
  | forall_ x φ ih =>
      simp only [Formula.stripForalls]
      cases h : Formula.stripForalls φ with
      | mk xs body =>
          simpa [Formula.forallMany, h] using
            congrArg (Formula.forall_ x) ih
  | top => rfl
  | bot => rfl
  | eq _ _ => rfl
  | rel _ => rfl
  | and _ _ _ _ => rfl
  | or _ _ _ _ => rfl
  | not _ _ => rfl
  | imp _ _ _ _ => rfl
  | iff _ _ _ _ => rfl
  | exists_ _ _ _ => rfl

/- Stripping existential quantifiers is reversible. -/
theorem existsMany_stripExists
    (φ : Formula D Γ) :
    Formula.existsMany (Formula.stripExists φ).1
        (Formula.stripExists φ).2 = φ := by
  induction φ with
  | exists_ x φ ih =>
      simp only [Formula.stripExists]
      cases h : Formula.stripExists φ with
      | mk xs body =>
          simpa [Formula.existsMany, h] using
            congrArg (Formula.exists_ x) ih
  | top => rfl
  | bot => rfl
  | eq _ _ => rfl
  | rel _ => rfl
  | and _ _ _ _ => rfl
  | or _ _ _ _ => rfl
  | not _ _ => rfl
  | imp _ _ _ _ => rfl
  | iff _ _ _ _ => rfl
  | forall_ _ _ _ => rfl

/- Normalized data certified by the TGD recognizer. -/
structure TGDView
    (φ : Formula D Γ) where
  universals : List Var
  body : Formula D Γ
  existentials : List Var
  head : Formula D Γ
  formula_eq :
    φ = Formula.forallMany universals
      (.imp body
        (Formula.existsMany existentials head))
  universals_nodup : universals.Nodup
  existentials_nodup : existentials.Nodup
  prefixes_disjoint :
    universals.toFinset ∩ existentials.toFinset = ∅
  body_isConj : body.IsRelVarConj
  head_isConj : head.IsRelVarConj
  body_vars : body.allVars = universals.toFinset
  head_vars :
    head.allVars ⊆
      universals.toFinset ∪ existentials.toFinset
  existentials_used :
    existentials.toFinset ⊆ head.allVars

/- Normalized data certified by the EGD recognizer. -/
structure EGDView
    (φ : Formula D Γ) where
  universals : List Var
  body : Formula D Γ
  lhs : Var
  rhs : Var
  formula_eq :
    φ = Formula.forallMany universals
      (.imp body (.eq (.var lhs) (.var rhs)))
  universals_nodup : universals.Nodup
  body_isConj : body.IsRelVarConj
  body_vars : body.allVars = universals.toFinset
  lhs_mem : lhs ∈ body.allVars
  rhs_mem : rhs ∈ body.allVars

/- Extract a normalized TGD view without rechecking it. -/
def tgdView
    (φ : Formula D Γ)
    (hTGD : φ.IsTGD) : TGDView φ := by
  cases hForall : Formula.stripForalls φ with
  | mk universals matrix =>
      cases matrix with
      | imp body rhs =>
          cases hExists : Formula.stripExists rhs with
          | mk existentials head =>
              have hProps :
                  universals.Nodup ∧
                  existentials.Nodup ∧
                  universals.toFinset ∩
                      existentials.toFinset = ∅ ∧
                  body.IsRelVarConj ∧
                  head.IsRelVarConj ∧
                  body.allVars = universals.toFinset ∧
                  head.allVars ⊆
                    universals.toFinset ∪
                      existentials.toFinset ∧
                  existentials.toFinset ⊆
                    head.allVars := by
                unfold Formula.IsTGD at hTGD
                simp only [Formula.isTGD,
                  hForall] at hTGD
                rw [hExists] at hTGD
                exact of_decide_eq_true hTGD
              have hOuter := forallMany_stripForalls φ
              rw [hForall] at hOuter
              have hInner := existsMany_stripExists rhs
              rw [hExists] at hInner
              have hOuter' :
                  Formula.forallMany universals
                      (.imp body rhs) = φ := by
                simpa using hOuter
              have hInner' :
                  Formula.existsMany existentials head =
                    rhs := by
                simpa using hInner
              exact
                { universals := universals
                  body := body
                  existentials := existentials
                  head := head
                  formula_eq := by
                    rw [hInner']
                    exact hOuter'.symm
                  universals_nodup := hProps.1
                  existentials_nodup := hProps.2.1
                  prefixes_disjoint := hProps.2.2.1
                  body_isConj := hProps.2.2.2.1
                  head_isConj := hProps.2.2.2.2.1
                  body_vars := hProps.2.2.2.2.2.1
                  head_vars :=
                    hProps.2.2.2.2.2.2.1
                  existentials_used :=
                    hProps.2.2.2.2.2.2.2 }
      | top =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | bot =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | eq _ _ =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | rel _ =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | and _ _ =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | or _ _ =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | not _ =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | iff _ _ =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | forall_ _ _ =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD
      | exists_ _ _ =>
          simp [Formula.IsTGD, Formula.isTGD,
            hForall] at hTGD

/- Extract a normalized EGD view without rechecking it. -/
def egdView
    (φ : Formula D Γ)
    (hEGD : φ.IsEGD) : EGDView φ := by
  cases hForall : Formula.stripForalls φ with
  | mk universals matrix =>
      cases matrix with
      | imp body head =>
          cases head with
          | eq lhs rhs =>
              cases lhs with
              | var x =>
                  cases rhs with
                  | var y =>
                      have hProps :
                          universals.Nodup ∧
                          body.IsRelVarConj ∧
                          body.allVars =
                            universals.toFinset ∧
                          x ∈ body.allVars ∧
                          y ∈ body.allVars := by
                        unfold Formula.IsEGD at hEGD
                        rw [Formula.isEGD,
                          hForall] at hEGD
                        exact of_decide_eq_true hEGD
                      have hOuter :=
                        forallMany_stripForalls φ
                      rw [hForall] at hOuter
                      exact
                        { universals := universals
                          body := body
                          lhs := x
                          rhs := y
                          formula_eq := hOuter.symm
                          universals_nodup := hProps.1
                          body_isConj := hProps.2.1
                          body_vars := hProps.2.2.1
                          lhs_mem := hProps.2.2.2.1
                          rhs_mem := hProps.2.2.2.2 }
                  | const _ =>
                      simp [Formula.IsEGD,
                        Formula.isEGD, hForall] at hEGD
              | const _ =>
                  simp [Formula.IsEGD,
                    Formula.isEGD, hForall] at hEGD
          | top =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | bot =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | rel _ =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | and _ _ =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | or _ _ =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | not _ =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | imp _ _ =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | iff _ _ =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | forall_ _ _ =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
          | exists_ _ _ =>
              simp [Formula.IsEGD, Formula.isEGD,
                hForall] at hEGD
      | top =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | bot =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | eq _ _ =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | rel _ =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | and _ _ =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | or _ _ =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | not _ =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | iff _ _ =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | forall_ _ _ =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD
      | exists_ _ _ =>
          simp [Formula.IsEGD, Formula.isEGD,
            hForall] at hEGD

end Compile

end Dependency

end RelCalc

------------------------------------------------------------
-- Datalog Body Compilation
------------------------------------------------------------

namespace RelCalc

namespace Dependency

namespace Compile

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The two ordered atom-variable views coincide. -/
theorem tupleVarList_eq_varList
    (a : RelAtom D Γ) :
    RelTerm.tupleVarList a.args = a.varList := by
  unfold RelTerm.tupleVarList RelAtom.varList
  induction a.args.toList with
  | nil =>
      rfl
  | cons t ts ih =>
      cases t <;>
        simp [RelTerm.listVarList, RelTerm.varList,
          RelTerm.var?, ih]

/- Variable-only evidence is a constant-free certificate. -/
def atomConstFree
    (a : RelAtom D Γ)
    (h : ∀ i, (a.args.get i).IsVar) :
    a.ConstFree := by
  intro i
  cases hArg : a.args.get i with
  | var _ =>
      trivial
  | const _ =>
      simpa [hArg, RelTerm.IsVar] using h i

/- Flatten a relational conjunction to a Datalog body. -/
def relBody :
    (φ : Formula D Γ) →
      φ.IsRelVarConj → Datalog.Body D Γ
| .rel a, _ => [.rel a]
| .and φ ψ, h =>
    relBody φ h.1 ++ relBody ψ h.2
| .top, h => False.elim h
| .bot, h => False.elim h
| .eq _ _, h => False.elim h
| .or _ _, h => False.elim h
| .not _, h => False.elim h
| .imp _ _, h => False.elim h
| .iff _ _, h => False.elim h
| .forall_ _ _, h => False.elim h
| .exists_ _ _, h => False.elim h

/- Satisfaction distributes over body append. -/
theorem bodySatisfied_append
    (body₁ body₂ : Datalog.Body D Γ)
    (I : Instance D Γ)
    (σ : Assign D) :
    Datalog.Body.Satisfied (body₁ ++ body₂) I σ ↔
      Datalog.Body.Satisfied body₁ I σ ∧
        Datalog.Body.Satisfied body₂ I σ := by
  induction body₁ with
  | nil =>
      simp [Datalog.Body.Satisfied]
  | cons atom body ih =>
      simp [Datalog.Body.Satisfied, ih, and_assoc]

/- Flattening preserves conjunction truth. -/
theorem relBody_satisfied_iff
    (φ : Formula D Γ)
    (hConj : φ.IsRelVarConj)
    (Q : Set D)
    (I : Instance D Γ)
    (σ : Assign D) :
    Datalog.Body.Satisfied (relBody φ hConj) I σ ↔
      Formula.ArbitraryAssignSatIn Q I σ φ := by
  induction φ with
  | rel a =>
      simp only [relBody, Datalog.Body.Satisfied,
        Datalog.Atom.Sat, and_true,
        Formula.ArbitraryAssignSatIn]
  | and φ ψ ihφ ihψ =>
      rw [relBody, bodySatisfied_append]
      simp only [Formula.ArbitraryAssignSatIn]
      exact and_congr
        (ihφ hConj.1) (ihψ hConj.2)
  | top => cases hConj
  | bot => cases hConj
  | eq _ _ => cases hConj
  | or _ _ _ _ => cases hConj
  | not _ _ => cases hConj
  | imp _ _ _ _ => cases hConj
  | iff _ _ _ _ => cases hConj
  | forall_ _ _ _ => cases hConj
  | exists_ _ _ _ => cases hConj

/- Flattening preserves ordered relational variables. -/
theorem relBody_relVarList_eq
    (φ : Formula D Γ)
    (hConj : φ.IsRelVarConj) :
    Datalog.Body.relVarList (relBody φ hConj) =
      φ.allVarList := by
  induction φ with
  | rel a =>
      simp [relBody, Datalog.Body.relVarList,
        Datalog.Atom.listRelVarList,
        Datalog.Atom.relVarList,
        Formula.allVarList, tupleVarList_eq_varList]
  | and φ ψ ihφ ihψ =>
      simp only [relBody, Datalog.Body.relVarList,
        Datalog.Atom.listRelVarList,
        List.map_append, List.flatten_append,
        Formula.allVarList]
      change
        Datalog.Body.relVarList (relBody φ hConj.1) ++
          Datalog.Body.relVarList (relBody ψ hConj.2) =
            φ.allVarList ++ ψ.allVarList
      rw [ihφ hConj.1, ihψ hConj.2]
  | top => cases hConj
  | bot => cases hConj
  | eq _ _ => cases hConj
  | or _ _ _ _ => cases hConj
  | not _ _ => cases hConj
  | imp _ _ _ _ => cases hConj
  | iff _ _ _ _ => cases hConj
  | forall_ _ _ _ => cases hConj
  | exists_ _ _ _ => cases hConj

/- Flattened bodies contain only relational atoms. -/
theorem relBody_varList_eq_relVarList
    (φ : Formula D Γ)
    (hConj : φ.IsRelVarConj) :
    Datalog.Body.varList (relBody φ hConj) =
      Datalog.Body.relVarList (relBody φ hConj) := by
  induction φ with
  | rel a =>
      simp [relBody, Datalog.Body.varList,
        Datalog.Body.relVarList,
        Datalog.Atom.listVarList,
        Datalog.Atom.listRelVarList,
        Datalog.Atom.varList,
        Datalog.Atom.relVarList]
  | and φ ψ ihφ ihψ =>
      simp only [relBody, Datalog.Body.varList,
        Datalog.Body.relVarList,
        Datalog.Atom.listVarList,
        Datalog.Atom.listRelVarList,
        List.map_append, List.flatten_append]
      change
        Datalog.Body.varList (relBody φ hConj.1) ++
            Datalog.Body.varList (relBody ψ hConj.2) =
          Datalog.Body.relVarList (relBody φ hConj.1) ++
            Datalog.Body.relVarList (relBody ψ hConj.2)
      rw [ihφ hConj.1, ihψ hConj.2]
  | top => cases hConj
  | bot => cases hConj
  | eq _ _ => cases hConj
  | or _ _ _ _ => cases hConj
  | not _ _ => cases hConj
  | imp _ _ _ _ => cases hConj
  | iff _ _ _ _ => cases hConj
  | forall_ _ _ _ => cases hConj
  | exists_ _ _ _ => cases hConj

/- Flattened relational conjunctions are safe bodies. -/
theorem relBody_safe
    (φ : Formula D Γ)
    (hConj : φ.IsRelVarConj) :
    Datalog.Body.RelationallySafe (relBody φ hConj) := by
  intro x hx
  have hxList :
      x ∈ Datalog.Body.varList (relBody φ hConj) := by
    simpa [Datalog.Body.vars, Datalog.Atom.vars,
      Datalog.Body.varList] using hx
  have hxRelList :
      x ∈ Datalog.Body.relVarList (relBody φ hConj) := by
    rw [← relBody_varList_eq_relVarList φ hConj]
    exact hxList
  simpa [Datalog.Body.HasRelVar,
    Datalog.Body.relVars, Datalog.Atom.relVars,
    Datalog.Body.relVarList] using hxRelList

/- Every source variable has a relational body position. -/
theorem relBody_hasRelVar
    (φ : Formula D Γ)
    (hConj : φ.IsRelVarConj)
    {x : Var}
    (hx : x ∈ φ.allVars) :
    Datalog.Body.HasRelVar (relBody φ hConj) x := by
  have hxList : x ∈ φ.allVarList :=
    Formula.mem_allVarList_of_mem_allVars hx
  have hxRelList :
      x ∈ Datalog.Body.relVarList (relBody φ hConj) := by
    rw [relBody_relVarList_eq φ hConj]
    exact hxList
  simpa [Datalog.Body.HasRelVar,
    Datalog.Body.relVars, Datalog.Atom.relVars,
    Datalog.Body.relVarList] using hxRelList

/- Compile a conjunction onto ordered output variables. -/
def projectRelBody
    (φ : Formula D Γ)
    (hConj : φ.IsRelVarConj)
    (xs : List Var)
    (hVars : ∀ x, x ∈ xs → x ∈ φ.allVars) :
    RAExpr D Γ xs.length :=
  Datalog.Body.projectVars
    (relBody φ hConj) xs
    (fun x hx =>
      relBody_hasRelVar φ hConj (hVars x hx))

/- Projected conjunctions expose satisfying assignments. -/
theorem projectRelBody_correct
    (φ : Formula D Γ)
    (hConj : φ.IsRelVarConj)
    (xs : List Var)
    (hVars : ∀ x, x ∈ xs → x ∈ φ.allVars)
    (I : Instance D Γ)
    (t : Tuple D xs.length) :
    t ∈ (projectRelBody φ hConj xs hVars).eval I ↔
      ∃ σ : Assign D,
        Formula.ArbitraryAssignSatIn
            (Set.univ : Set D) I σ φ ∧
          Assign.toListTuple xs σ = t := by
  unfold projectRelBody
  rw [Datalog.Body.projectVars_correct
    _ _ (relBody_safe φ hConj)]
  constructor
  · rintro ⟨σ, hSat, hTuple⟩
    exact ⟨σ,
      (relBody_satisfied_iff
        φ hConj Set.univ I σ).1 hSat,
      hTuple⟩
  · rintro ⟨σ, hSat, hTuple⟩
    exact ⟨σ,
      (relBody_satisfied_iff
        φ hConj Set.univ I σ).2 hSat,
      hTuple⟩

end Compile

end Dependency

end RelCalc

------------------------------------------------------------
-- Quantifier Prefix Semantics
------------------------------------------------------------

namespace RelCalc

namespace Dependency

namespace Compile

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Two assignments agree outside a variable list. -/
def AgreesOutside
    (σ τ : Assign D)
    (xs : List Var) : Prop :=
  ∀ x, x ∉ xs → σ x = τ x

/- Universal prefixes quantify all bounded assignments. -/
theorem arbitrary_forallMany_iff :
    ∀ (xs : List Var), xs.Nodup →
      ∀ (φ : Formula D Γ)
        (Q : Set D)
        (I : Instance D Γ)
        (σ : Assign D),
        Formula.ArbitraryAssignSatIn Q I σ
            (Formula.forallMany xs φ) ↔
          ∀ τ : Assign D,
            Assign.MapsInto τ xs.toFinset Q →
            AgreesOutside σ τ xs →
            Formula.ArbitraryAssignSatIn Q I τ φ
| [], _, φ, Q, I, σ => by
    constructor
    · intro h τ _hMap hOutside
      have hEq : σ = τ := by
        funext x
        exact hOutside x (by simp)
      simpa [Formula.forallMany, hEq] using h
    · intro h
      exact h σ
        (by intro x hx; simp at hx)
        (by intro x _; rfl)
| x :: xs, hNodup, φ, Q, I, σ => by
    have hx : x ∉ xs := (List.nodup_cons.mp hNodup).1
    have hTail := (List.nodup_cons.mp hNodup).2
    rw [Formula.forallMany]
    constructor
    · intro h τ hMap hOutside
      have hxQ : Q (τ x) :=
        hMap x (by simp)
      have hRest := h (τ x) hxQ
      apply (arbitrary_forallMany_iff
        xs hTail φ Q I
        (Assign.update σ x (τ x))).1 hRest τ
      · intro y hy
        exact hMap y (by simp [hy])
      · intro y hy
        by_cases hyx : y = x
        · subst y
          simp [Assign.update]
        · have hyAll : y ∉ x :: xs := by
            simp [hyx, hy]
          simp [Assign.update, hyx,
            hOutside y hyAll]
    · intro h d hd
      apply (arbitrary_forallMany_iff
        xs hTail φ Q I
        (Assign.update σ x d)).2
      intro τ hMap hOutside
      apply h τ
      · intro y hy
        have hyCases : y = x ∨ y ∈ xs := by
          simpa using hy
        rcases hyCases with rfl | hyTail
        · have hEq := hOutside _ hx
          have hEq' : d = τ y := by
            simpa [Assign.update] using hEq
          exact hEq' ▸ hd
        · exact hMap y (by simpa using hyTail)
      · intro y hy
        have hyx : y ≠ x := by
          intro hEq
          subst y
          exact hy (by simp)
        have hyTail : y ∉ xs := by
          intro hMem
          exact hy (by simp [hMem])
        have hEq := hOutside y hyTail
        simpa [Assign.update, hyx] using hEq

/- Existential prefixes expose one bounded assignment. -/
theorem arbitrary_existsMany_iff :
    ∀ (xs : List Var), xs.Nodup →
      ∀ (φ : Formula D Γ)
        (Q : Set D)
        (I : Instance D Γ)
        (σ : Assign D),
        Formula.ArbitraryAssignSatIn Q I σ
            (Formula.existsMany xs φ) ↔
          ∃ τ : Assign D,
            Assign.MapsInto τ xs.toFinset Q ∧
            AgreesOutside σ τ xs ∧
            Formula.ArbitraryAssignSatIn Q I τ φ
| [], _, φ, Q, I, σ => by
    constructor
    · intro h
      exact
        ⟨σ,
          by intro x hx; simp at hx,
          by intro x _; rfl,
          by simpa [Formula.existsMany] using h⟩
    · rintro ⟨τ, _hMap, hOutside, hSat⟩
      have hEq : σ = τ := by
        funext x
        exact hOutside x (by simp)
      simpa [Formula.existsMany, hEq] using hSat
| x :: xs, hNodup, φ, Q, I, σ => by
    have hx : x ∉ xs := (List.nodup_cons.mp hNodup).1
    have hTail := (List.nodup_cons.mp hNodup).2
    rw [Formula.existsMany]
    constructor
    · rintro ⟨d, hd, hRest⟩
      rcases (arbitrary_existsMany_iff
          xs hTail φ Q I
          (Assign.update σ x d)).1 hRest with
        ⟨τ, hMap, hOutside, hSat⟩
      refine ⟨τ, ?_, ?_, hSat⟩
      · intro y hy
        have hyCases : y = x ∨ y ∈ xs := by
          simpa using hy
        rcases hyCases with rfl | hyTail
        · have hEq := hOutside _ hx
          have hEq' : d = τ y := by
            simpa [Assign.update] using hEq
          exact hEq' ▸ hd
        · exact hMap y (by simpa using hyTail)
      · intro y hy
        have hyx : y ≠ x := by
          intro hEq
          subst y
          exact hy (by simp)
        have hyTail : y ∉ xs := by
          intro hMem
          exact hy (by simp [hMem])
        have hEq := hOutside y hyTail
        simpa [Assign.update, hyx] using hEq
    · rintro ⟨τ, hMap, hOutside, hSat⟩
      refine ⟨τ x, hMap x (by simp), ?_⟩
      apply (arbitrary_existsMany_iff
        xs hTail φ Q I
        (Assign.update σ x (τ x))).2
      refine ⟨τ, ?_, ?_, hSat⟩
      · intro y hy
        exact hMap y (by simp [hy])
      · intro y hy
        by_cases hyx : y = x
        · subst y
          simp [Assign.update]
        · have hyAll : y ∉ x :: xs := by
            simp [hyx, hy]
          simpa [Assign.update, hyx] using
            hOutside y hyAll

end Compile

end Dependency

end RelCalc

------------------------------------------------------------
-- Dependency Semantic Support
------------------------------------------------------------

namespace RelCalc

namespace Dependency

namespace Compile

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Relational conjunction truth is domain-independent. -/
theorem relVarConj_domain_irrel :
    ∀ (φ : Formula D Γ),
      φ.IsRelVarConj →
      ∀ (Q S : Set D)
        (I : Instance D Γ)
        (σ : Assign D),
        Formula.ArbitraryAssignSatIn Q I σ φ ↔
          Formula.ArbitraryAssignSatIn S I σ φ
| .rel _, _, _, _, _, _ => Iff.rfl
| .and φ ψ, hConj, Q, S, I, σ => by
    simp only [Formula.ArbitraryAssignSatIn]
    exact and_congr
      (relVarConj_domain_irrel
        φ hConj.1 Q S I σ)
      (relVarConj_domain_irrel
        ψ hConj.2 Q S I σ)
| .top, hConj, _, _, _, _ => False.elim hConj
| .bot, hConj, _, _, _, _ => False.elim hConj
| .eq _ _, hConj, _, _, _, _ => False.elim hConj
| .or _ _, hConj, _, _, _, _ => False.elim hConj
| .not _, hConj, _, _, _, _ => False.elim hConj
| .imp _ _, hConj, _, _, _, _ => False.elim hConj
| .iff _ _, hConj, _, _, _, _ => False.elim hConj
| .forall_ _ _, hConj, _, _, _, _ => False.elim hConj
| .exists_ _ _, hConj, _, _, _, _ => False.elim hConj

/-
  Satisfying relational variables take active-domain
  values.
-/
theorem relVarConj_value_mem_adom :
    ∀ (φ : Formula D Γ)
      (_hConj : φ.IsRelVarConj)
      (I : Instance D Γ)
      (σ : Assign D),
      Formula.ArbitraryAssignSatIn
          (Set.univ : Set D) I σ φ →
        ∀ x, x ∈ φ.allVars → σ x ∈ I.Adom
| .rel a, hConj, I, σ, hSat => by
    intro x hx
    have hFree := atomConstFree a hConj
    have hList : x ∈ a.varList := by
      have hAll :=
        Formula.mem_allVarList_of_mem_allVars hx
      simpa [Formula.allVarList,
        Formula.allVars, tupleVarList_eq_varList]
        using hAll
    have hOver : (a.evalTuple σ).isTupleOver I.Adom :=
      I.isTupleOver_Adom_of_mem
        (by simpa [RelAtom.Sat] using hSat)
    exact a.value_mem_of_var_mem_evalTuple_over
      hOver hList
| .and φ ψ, hConj, I, σ, hSat => by
    intro x hx
    rcases Finset.mem_union.mp
        (by simpa [Formula.allVars] using hx) with
      hxLeft | hxRight
    · exact relVarConj_value_mem_adom
        φ hConj.1 I σ hSat.1 x hxLeft
    · exact relVarConj_value_mem_adom
        ψ hConj.2 I σ hSat.2 x hxRight
| .top, hConj, _, _, _ => False.elim hConj
| .bot, hConj, _, _, _ => False.elim hConj
| .eq _ _, hConj, _, _, _ => False.elim hConj
| .or _ _, hConj, _, _, _ => False.elim hConj
| .not _, hConj, _, _, _ => False.elim hConj
| .imp _ _, hConj, _, _, _ => False.elim hConj
| .iff _ _, hConj, _, _, _ => False.elim hConj
| .forall_ _ _, hConj, _, _, _ => False.elim hConj
| .exists_ _ _, hConj, _, _, _ => False.elim hConj

/- Copy `src` onto `xs`, retaining `base` elsewhere. -/
def overwriteOn
    (base src : Assign D)
    (xs : List Var) : Assign D :=
  fun x => if x ∈ xs then src x else base x

/-
  Overwriting agrees with the source on listed variables.
-/
omit [Domain D] in
theorem overwriteOn_mem
    (base src : Assign D)
    (xs : List Var)
    {x : Var}
    (hx : x ∈ xs) :
    overwriteOn base src xs x = src x := by
  simp [overwriteOn, hx]

/- Overwriting agrees with the base off the list. -/
omit [Domain D] in
theorem overwriteOn_not_mem
    (base src : Assign D)
    (xs : List Var)
    {x : Var}
    (hx : x ∉ xs) :
    overwriteOn base src xs x = base x := by
  simp [overwriteOn, hx]

/- Equal assignment tuples agree on listed variables. -/
omit [Domain D] in
theorem agree_of_toListTuple_eq
    (xs : List Var)
    {σ τ : Assign D}
    (hTuple :
      Assign.toListTuple xs σ =
        Assign.toListTuple xs τ) :
    ∀ x, x ∈ xs → σ x = τ x := by
  intro x hx
  rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
  have hCoord := congrArg
    (fun t : Tuple D xs.length => t.get i) hTuple
  have hAt : σ (xs.get i) = τ (xs.get i) := by
    simpa [Assign.toListTuple, Vector.get] using hCoord
  exact (congrArg σ hi.symm).trans
    (hAt.trans (congrArg τ hi))

end Compile

end Dependency

end RelCalc

------------------------------------------------------------
-- Dependency Guard Compilation
------------------------------------------------------------

namespace RelCalc

namespace Dependency

namespace Compile

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Universal variables also used by the TGD head. -/
def TGDView.frontier
    {φ : Formula D Γ}
    (v : TGDView φ) : List Var :=
  v.universals.filter fun x => x ∈ v.head.allVars

/- Frontier variables occur in the body. -/
theorem TGDView.frontier_mem_body
    {φ : Formula D Γ}
    (v : TGDView φ)
    {x : Var}
    (hx : x ∈ v.frontier) :
    x ∈ v.body.allVars := by
  rw [v.body_vars]
  simpa using (List.mem_filter.mp hx).1

/- Frontier variables occur in the head. -/
theorem TGDView.frontier_mem_head
    {φ : Formula D Γ}
    (v : TGDView φ)
    {x : Var}
    (hx : x ∈ v.frontier) :
    x ∈ v.head.allVars := by
  exact of_decide_eq_true (List.mem_filter.mp hx).2

/- Compile one normalized TGD to containment. -/
def TGDView.toQFAssert
    {φ : Formula D Γ}
    (v : TGDView φ) : Whiel.QFAssertExpr D Γ :=
  let bodyQuery :=
    projectRelBody v.body v.body_isConj v.frontier
      fun _ hx => v.frontier_mem_body hx
  let headQuery :=
    projectRelBody v.head v.head_isConj v.frontier
      fun _ hx => v.frontier_mem_head hx
  .subset bodyQuery.clean headQuery.clean

/- Compile one certified TGD to containment. -/
def compileTGD
    (φ : Formula D Γ)
    (hTGD : φ.IsTGD) : Whiel.QFAssertExpr D Γ :=
  (tgdView φ hTGD).toQFAssert

/- TGD guard truth is active-domain TGD truth. -/
theorem TGDView.toQFAssert_correct
    {φ : Formula D Γ}
    (v : TGDView φ)
    (I : Instance D Γ) :
    v.toQFAssert.eval I ↔
      ∀ σ₀ : Assign D,
        Formula.ArbitraryAssignSatIn
          (↑I.Adom : Set D) I σ₀
          (Formula.forallMany v.universals
            (.imp v.body
              (Formula.existsMany
                v.existentials v.head))) := by
  let bodySub :
      ∀ x, x ∈ v.frontier → x ∈ v.body.allVars :=
    fun _ hx => v.frontier_mem_body hx
  let headSub :
      ∀ x, x ∈ v.frontier → x ∈ v.head.allVars :=
    fun _ hx => v.frontier_mem_head hx
  let bodyQuery :=
    projectRelBody v.body v.body_isConj
      v.frontier bodySub
  let headQuery :=
    projectRelBody v.head v.head_isConj
      v.frontier headSub
  change bodyQuery.clean.eval I ⊆
      headQuery.clean.eval I ↔ _
  simp only [RAExpr.eval_clean]
  constructor
  · intro hSubset σ₀
    apply (arbitrary_forallMany_iff
      v.universals v.universals_nodup _
      (↑I.Adom : Set D) I σ₀).2
    intro τ _hMap _hOutside
    simp only [Formula.ArbitraryAssignSatIn]
    intro hBodyAdom
    have hBody :
        Formula.ArbitraryAssignSatIn
          (Set.univ : Set D) I τ v.body :=
      (relVarConj_domain_irrel
        v.body v.body_isConj _ Set.univ I τ).1
        hBodyAdom
    let t := Assign.toListTuple v.frontier τ
    have htBody : t ∈ bodyQuery.eval I := by
      apply (projectRelBody_correct
        v.body v.body_isConj v.frontier
        bodySub I t).2
      exact ⟨τ, hBody, rfl⟩
    have htHead := hSubset htBody
    rcases (projectRelBody_correct
        v.head v.head_isConj v.frontier
        headSub I t).1 htHead with
      ⟨ρ, hHead, hTuple⟩
    let η := overwriteOn τ ρ v.existentials
    apply (arbitrary_existsMany_iff
      v.existentials v.existentials_nodup
      v.head (↑I.Adom : Set D) I τ).2
    refine ⟨η, ?_, ?_, ?_⟩
    · intro x hx
      have hxList : x ∈ v.existentials := by
        simpa using hx
      have hxHead : x ∈ v.head.allVars :=
        v.existentials_used hx
      have hxAdom : ρ x ∈ I.Adom :=
        relVarConj_value_mem_adom
          v.head v.head_isConj I ρ hHead x hxHead
      simpa [η, overwriteOn_mem τ ρ
        v.existentials hxList] using hxAdom
    · intro x hx
      exact (overwriteOn_not_mem τ ρ
        v.existentials hx).symm
    · have hHeadAdom :
          Formula.ArbitraryAssignSatIn
            (↑I.Adom : Set D) I ρ v.head :=
        (relVarConj_domain_irrel
          v.head v.head_isConj Set.univ _ I ρ).1
          hHead
      apply (Formula.holdsIn_eq_of_agreeOn_freeVars
        v.head (Q := (↑I.Adom : Set D)) (I := I)
        (σ := ρ) (τ := η) ?_).1 hHeadAdom
      intro x hxFree
      have hxAll : x ∈ v.head.allVars :=
        v.head.freeVars_subset_allVars hxFree
      rcases Finset.mem_union.mp (v.head_vars hxAll) with
        hxUniversal | hxExistential
      · have hxUList : x ∈ v.universals := by
          simpa using hxUniversal
        have hxFrontier : x ∈ v.frontier := by
          apply List.mem_filter.mpr
          exact ⟨hxUList, decide_eq_true hxAll⟩
        have hDisjoint :
            Disjoint v.universals.toFinset
              v.existentials.toFinset := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          exact v.prefixes_disjoint
        have hxNotExist : x ∉ v.existentials := by
          intro hxE
          exact (Finset.disjoint_left.mp hDisjoint)
            hxUniversal (by simpa using hxE)
        have hFrontier := agree_of_toListTuple_eq
          v.frontier hTuple.symm x hxFrontier
        change ρ x = overwriteOn τ ρ v.existentials x
        rw [overwriteOn_not_mem τ ρ
          v.existentials hxNotExist]
        exact hFrontier.symm
      · have hxEList : x ∈ v.existentials := by
          simpa using hxExistential
        exact (overwriteOn_mem τ ρ
          v.existentials hxEList).symm
  · intro hSource t htBody
    rcases (projectRelBody_correct
        v.body v.body_isConj v.frontier
        bodySub I t).1 htBody with
      ⟨τ, hBody, hTuple⟩
    have hMap :
        Assign.MapsInto τ v.universals.toFinset
          (↑I.Adom : Set D) := by
      intro x hx
      have hxBody : x ∈ v.body.allVars := by
        rw [v.body_vars]
        exact hx
      exact relVarConj_value_mem_adom
        v.body v.body_isConj I τ hBody x hxBody
    have hMatrix :=
      (arbitrary_forallMany_iff
        v.universals v.universals_nodup _
        (↑I.Adom : Set D) I τ).1
        (hSource τ) τ hMap (by intro x _; rfl)
    have hBodyAdom :
        Formula.ArbitraryAssignSatIn
          (↑I.Adom : Set D) I τ v.body :=
      (relVarConj_domain_irrel
        v.body v.body_isConj Set.univ _ I τ).1 hBody
    have hExists := hMatrix hBodyAdom
    rcases (arbitrary_existsMany_iff
        v.existentials v.existentials_nodup
        v.head (↑I.Adom : Set D) I τ).1 hExists with
      ⟨ρ, _hMapExist, hOutside, hHeadAdom⟩
    have hHead :
        Formula.ArbitraryAssignSatIn
          (Set.univ : Set D) I ρ v.head :=
      (relVarConj_domain_irrel
        v.head v.head_isConj _ Set.univ I ρ).1
          hHeadAdom
    apply (projectRelBody_correct
      v.head v.head_isConj v.frontier
      headSub I t).2
    refine ⟨ρ, hHead, ?_⟩
    rw [← hTuple]
    apply Vector.ext
    intro i hi
    let j : Fin v.frontier.length := ⟨i, hi⟩
    have hxFrontier : v.frontier[i] ∈ v.frontier :=
      List.getElem_mem hi
    have hxUniversal : v.frontier[i] ∈ v.universals :=
      (List.mem_filter.mp hxFrontier).1
    have hDisjoint :
        Disjoint v.universals.toFinset
          v.existentials.toFinset := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact v.prefixes_disjoint
    have hxNotExist : v.frontier[i] ∉ v.existentials := by
      intro hxE
      exact (Finset.disjoint_left.mp hDisjoint)
        (by simpa using hxUniversal)
        (by simpa using hxE)
    have hAgree := hOutside v.frontier[i] hxNotExist
    simpa [Assign.toListTuple, Vector.get, j]
      using hAgree.symm

/- The EGD body with its equality remains safe. -/
theorem EGDView.extendedBody_safe
    {φ : Formula D Γ}
    (v : EGDView φ) :
    Datalog.Body.RelationallySafe
      (relBody v.body v.body_isConj ++
        [.eq (.var v.lhs) (.var v.rhs)]) := by
  intro x hx
  have hxCases :
      x = v.lhs ∨ x = v.rhs ∨
        x ∈ Datalog.Body.vars
          (relBody v.body v.body_isConj) := by
    simpa [Datalog.Body.vars, Datalog.Atom.vars,
      Datalog.Atom.listVarList,
      Datalog.Atom.varList, RelTerm.var?]
      using hx
  have hxRel :
      Datalog.Body.HasRelVar
        (relBody v.body v.body_isConj) x := by
    rcases hxCases with rfl | rfl | hxOld
    · exact relBody_hasRelVar
        v.body v.body_isConj v.lhs_mem
    · exact relBody_hasRelVar
        v.body v.body_isConj v.rhs_mem
    · exact relBody_safe v.body v.body_isConj x hxOld
  simpa [Datalog.Body.HasRelVar,
    Datalog.Body.relVars, Datalog.Atom.relVars,
    Datalog.Body.relVarList,
    Datalog.Atom.listRelVarList,
    Datalog.Atom.relVarList] using hxRel

/- Compile one normalized EGD to query equality. -/
def EGDView.toQFAssert
    {φ : Formula D Γ}
    (v : EGDView φ) : Whiel.QFAssertExpr D Γ :=
  let body := relBody v.body v.body_isConj
  let lhsQuery := Datalog.Body.selectedProduct body
  let rhsBody :=
    body ++ [.eq (.var v.lhs) (.var v.rhs)]
  let rhsQuery := RAExpr.castArity
    (Datalog.Body.arity_append_eq
      body (.var v.lhs) (.var v.rhs)).symm
    (Datalog.Body.selectedProduct rhsBody)
  .eq lhsQuery.clean rhsQuery.clean

/- Compile one certified EGD to query equality. -/
def compileEGD
    (φ : Formula D Γ)
    (hEGD : φ.IsEGD) : Whiel.QFAssertExpr D Γ :=
  (egdView φ hEGD).toQFAssert

/- EGD guard truth is active-domain EGD truth. -/
theorem EGDView.toQFAssert_correct
    {φ : Formula D Γ}
    (v : EGDView φ)
    (I : Instance D Γ) :
    v.toQFAssert.eval I ↔
      ∀ σ₀ : Assign D,
        Formula.ArbitraryAssignSatIn
          (↑I.Adom : Set D) I σ₀
          (Formula.forallMany v.universals
            (.imp v.body
              (.eq (.var v.lhs) (.var v.rhs)))) := by
  let body := relBody v.body v.body_isConj
  let rhsBody :=
    body ++ [.eq (.var v.lhs) (.var v.rhs)]
  let hAr :
      Datalog.Body.arity body =
        Datalog.Body.arity rhsBody :=
    (Datalog.Body.arity_append_eq
      body (.var v.lhs) (.var v.rhs)).symm
  let lhsQuery := Datalog.Body.selectedProduct body
  let rhsWide := Datalog.Body.selectedProduct rhsBody
  let rhsQuery := RAExpr.castArity hAr rhsWide
  change lhsQuery.clean.eval I = rhsQuery.clean.eval I ↔ _
  simp only [RAExpr.eval_clean]
  have hRelation :
      lhsQuery.eval I = rhsQuery.eval I ↔
        ∀ σ : Assign D,
          Formula.ArbitraryAssignSatIn
              (Set.univ : Set D) I σ v.body →
            σ v.lhs = σ v.rhs := by
    constructor
    · intro hQueries σ hBody
      have hBodySat :
          Datalog.Body.Satisfied body I σ :=
        (relBody_satisfied_iff
          v.body v.body_isConj Set.univ I σ).2 hBody
      have htLeft :
          Datalog.Body.productTuple σ body ∈
            lhsQuery.eval I := by
        apply (Datalog.Body.selectedProduct_correct
          body (relBody_safe v.body v.body_isConj)
          I _).2
        exact ⟨σ, hBodySat, rfl⟩
      have htRight :
          Datalog.Body.productTuple σ body ∈
            rhsQuery.eval I := by
        rw [← hQueries]
        exact htLeft
      have htWide :
          Tuple.castArity hAr.symm
              (Datalog.Body.productTuple σ body) ∈
            rhsWide.eval I :=
        (RAExpr.mem_eval_castArity
          hAr rhsWide I _).1 htRight
      rcases (Datalog.Body.selectedProduct_correct
          rhsBody v.extendedBody_safe I _).1 htWide with
        ⟨ρ, hRhs, hProduct⟩
      have hRhsParts :=
        (bodySatisfied_append body
          [.eq (.var v.lhs) (.var v.rhs)] I ρ).1
          hRhs
      have hρEq : ρ v.lhs = ρ v.rhs := by
        simpa [Datalog.Body.Satisfied,
          Datalog.Atom.Sat, RelTerm.eval]
          using hRhsParts.2
      have hBaseProduct :
          Datalog.Body.productTuple ρ body =
            Datalog.Body.productTuple σ body := by
        have hCast := congrArg
          (Tuple.castArity hAr) hProduct
        have hAppend :=
          Datalog.Body.productTuple_append_eq
            ρ body (.var v.lhs) (.var v.rhs)
        simpa [rhsBody, hAr,
          Tuple.castArity_symm] using
          hAppend.symm.trans hCast
      have hLhs :=
        Datalog.Body.eval_eq_of_productTuple_eq
          body σ ρ
          (relBody_hasRelVar
            v.body v.body_isConj v.lhs_mem)
          hBaseProduct.symm
      have hRhs :=
        Datalog.Body.eval_eq_of_productTuple_eq
          body σ ρ
          (relBody_hasRelVar
            v.body v.body_isConj v.rhs_mem)
          hBaseProduct.symm
      exact hLhs.trans (hρEq.trans hRhs.symm)
    · intro hAll
      apply Finset.ext
      intro t
      constructor
      · intro htLeft
        rcases (Datalog.Body.selectedProduct_correct
            body (relBody_safe v.body v.body_isConj)
            I t).1 htLeft with
          ⟨σ, hBodySat, hProduct⟩
        apply (RAExpr.mem_eval_castArity
          hAr rhsWide I t).2
        apply (Datalog.Body.selectedProduct_correct
          rhsBody v.extendedBody_safe I _).2
        refine ⟨σ, ?_, ?_⟩
        · apply (bodySatisfied_append body
            [.eq (.var v.lhs) (.var v.rhs)] I σ).2
          refine ⟨hBodySat, ?_⟩
          have hBody :
              Formula.ArbitraryAssignSatIn
                (Set.univ : Set D) I σ v.body :=
            (relBody_satisfied_iff
              v.body v.body_isConj Set.univ I σ).1
              hBodySat
          simpa [Datalog.Body.Satisfied,
            Datalog.Atom.Sat, RelTerm.eval]
            using hAll σ hBody
        · have hAppend :=
            Datalog.Body.productTuple_append_eq
              σ body (.var v.lhs) (.var v.rhs)
          rw [hProduct] at hAppend
          have hCast := congrArg
            (Tuple.castArity hAr.symm) hAppend
          simpa [rhsBody, hAr,
            Tuple.castArity_symm] using hCast
      · intro htRight
        have htWide :=
          (RAExpr.mem_eval_castArity
            hAr rhsWide I t).1 htRight
        rcases (Datalog.Body.selectedProduct_correct
            rhsBody v.extendedBody_safe I _).1 htWide with
          ⟨σ, hRhsSat, hProduct⟩
        apply (Datalog.Body.selectedProduct_correct
          body (relBody_safe v.body v.body_isConj)
          I t).2
        refine ⟨σ, ?_, ?_⟩
        · exact (bodySatisfied_append body
            [.eq (.var v.lhs) (.var v.rhs)] I σ).1
              hRhsSat |>.1
        · have hAppend :=
            Datalog.Body.productTuple_append_eq
              σ body (.var v.lhs) (.var v.rhs)
          rw [hProduct] at hAppend
          simpa [rhsBody, hAr,
            Tuple.castArity_symm] using hAppend.symm
  rw [hRelation]
  constructor
  · intro hAll σ₀
    apply (arbitrary_forallMany_iff
      v.universals v.universals_nodup _
      (↑I.Adom : Set D) I σ₀).2
    intro τ _hMap _hOutside
    simp only [Formula.ArbitraryAssignSatIn,
      RelTerm.eval]
    intro hBodyAdom
    apply hAll τ
    exact (relVarConj_domain_irrel
      v.body v.body_isConj _ Set.univ I τ).1
        hBodyAdom
  · intro hSource σ hBody
    have hMap :
        Assign.MapsInto σ v.universals.toFinset
          (↑I.Adom : Set D) := by
      intro x hx
      have hxBody : x ∈ v.body.allVars := by
        rw [v.body_vars]
        exact hx
      exact relVarConj_value_mem_adom
        v.body v.body_isConj I σ hBody x hxBody
    have hMatrix :=
      (arbitrary_forallMany_iff
        v.universals v.universals_nodup _
        (↑I.Adom : Set D) I σ).1
        (hSource σ) σ hMap (by intro x _; rfl)
    have hBodyAdom :
        Formula.ArbitraryAssignSatIn
          (↑I.Adom : Set D) I σ v.body :=
      (relVarConj_domain_irrel
        v.body v.body_isConj Set.univ
          (↑I.Adom : Set D) I σ).1 hBody
    exact hMatrix hBodyAdom

end Compile

end Dependency

end RelCalc

------------------------------------------------------------
-- Dependency Closure
------------------------------------------------------------

namespace RelCalc

namespace Dependency

namespace Compile

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Membership after repeated erasure. -/
theorem mem_foldr_erase_iff
    (xs : List Var)
    (S : Finset Var)
    (x : Var) :
    x ∈ xs.foldr (fun y T => T.erase y) S ↔
      x ∈ S ∧ x ∉ xs := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp [ih, and_left_comm]

/- Quantifying a cover of all free variables closes it. -/
theorem forallMany_isSentence
    (xs : List Var)
    (φ : Formula D Γ)
    (hCover : φ.freeVars ⊆ xs.toFinset) :
    (Formula.forallMany xs φ).IsSentence := by
  unfold Formula.IsSentence
  rw [Formula.freeVars_forallMany]
  apply Finset.ext
  intro x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hInfo := (mem_foldr_erase_iff
    xs φ.freeVars x).1 hx
  exact hInfo.2 (by simpa using hCover hInfo.1)

/- A normalized TGD is closed. -/
theorem TGDView.isSentence
    {φ : Formula D Γ}
    (v : TGDView φ) : φ.IsSentence := by
  rw [v.formula_eq]
  apply forallMany_isSentence
  intro x hx
  rcases Finset.mem_union.mp
      (by simpa [Formula.freeVars] using hx) with
    hxBody | hxExists
  · have hxAll := v.body.freeVars_subset_allVars hxBody
    rw [v.body_vars] at hxAll
    exact hxAll
  · rw [Formula.freeVars_existsMany] at hxExists
    have hInfo := (mem_foldr_erase_iff
      v.existentials v.head.freeVars x).1 hxExists
    have hxAll := v.head.freeVars_subset_allVars hInfo.1
    rcases Finset.mem_union.mp (v.head_vars hxAll) with
      hxUniversal | hxExistential
    · exact hxUniversal
    · exact False.elim
        (hInfo.2 (by simpa using hxExistential))

/- A normalized EGD is closed. -/
theorem EGDView.isSentence
    {φ : Formula D Γ}
    (v : EGDView φ) : φ.IsSentence := by
  rw [v.formula_eq]
  apply forallMany_isSentence
  intro x hx
  have hxCases :
      x = v.lhs ∨ x = v.rhs ∨
        x ∈ v.body.freeVars := by
    simpa [Formula.freeVars, RelTerm.vars] using hx
  rcases hxCases with rfl | rfl | hxBody
  · rw [← v.body_vars]
    exact v.lhs_mem
  · rw [← v.body_vars]
    exact v.rhs_mem
  · have hxAll := v.body.freeVars_subset_allVars hxBody
    rw [v.body_vars] at hxAll
    exact hxAll

/- TGD recognition proves closure. -/
theorem isSentence_of_isTGD
    (φ : Formula D Γ)
    (hTGD : φ.IsTGD) : φ.IsSentence :=
  (tgdView φ hTGD).isSentence

/- EGD recognition proves closure. -/
theorem isSentence_of_isEGD
    (φ : Formula D Γ)
    (hEGD : φ.IsEGD) : φ.IsSentence :=
  (egdView φ hEGD).isSentence

/- A variable-only term list has no constants. -/
theorem listConstants_eq_empty_of_isVar
    (ts : List (RelTerm D))
    (hVars : ∀ t ∈ ts, t.IsVar) :
    RelTerm.listConstants ts = ∅ := by
  induction ts with
  | nil =>
      rfl
  | cons t ts ih =>
      have ht := hVars t (by simp)
      have hts : ∀ u ∈ ts, u.IsVar := by
        intro u hu
        exact hVars u (by simp [hu])
      cases t with
      | var _ =>
          change ∅ ∪ RelTerm.listConstants ts = ∅
          rw [ih hts]
          simp
      | const _ =>
          cases ht

/- A variable-only atom has no constants. -/
theorem relAtom_constants_eq_empty_of_isVar
    (a : RelAtom D Γ)
    (hVars : ∀ i, (a.args.get i).IsVar) :
    a.constants = ∅ := by
  unfold RelAtom.constants RelTerm.tupleConstants
  apply listConstants_eq_empty_of_isVar
  intro t ht
  rcases List.mem_iff_get.mp ht with ⟨i, hi⟩
  let j : Fin (Γ.arity a.rel) :=
    ⟨i.1, by
      simpa [Vector.length_toList] using i.2⟩
  have hGet : a.args.get j = t := by
    change a.args[i.1] = t
    have hCoord :
        a.args.toList[i.1] = a.args[i.1] :=
      Vector.getElem_toList i.2
    exact hCoord.symm.trans hi
  simpa [hGet] using hVars j

/- A relation-variable conjunction has no constants. -/
theorem relVarConj_constants_eq_empty
    (φ : Formula D Γ)
    (hConj : φ.IsRelVarConj) :
    φ.constants = ∅ := by
  induction φ with
  | rel a =>
      exact relAtom_constants_eq_empty_of_isVar a hConj
  | and φ ψ ihφ ihψ =>
      simp only [Formula.constants]
      rw [ihφ hConj.1, ihψ hConj.2]
      simp
  | top => cases hConj
  | bot => cases hConj
  | eq _ _ => cases hConj
  | or _ _ _ _ => cases hConj
  | not _ _ => cases hConj
  | imp _ _ _ _ => cases hConj
  | iff _ _ _ _ => cases hConj
  | forall_ _ _ _ => cases hConj
  | exists_ _ _ _ => cases hConj

/- TGD recognition proves absence of constants. -/
theorem constants_eq_empty_of_isTGD
    (φ : Formula D Γ)
    (hTGD : φ.IsTGD) : φ.constants = ∅ := by
  let v := tgdView φ hTGD
  rw [v.formula_eq, Formula.constants_forallMany]
  simp only [Formula.constants,
    Formula.constants_existsMany]
  rw [relVarConj_constants_eq_empty
    v.body v.body_isConj]
  rw [relVarConj_constants_eq_empty
    v.head v.head_isConj]
  simp

/- EGD recognition proves absence of constants. -/
theorem constants_eq_empty_of_isEGD
    (φ : Formula D Γ)
    (hEGD : φ.IsEGD) : φ.constants = ∅ := by
  let v := egdView φ hEGD
  rw [v.formula_eq, Formula.constants_forallMany]
  simp [Formula.constants,
    relVarConj_constants_eq_empty
      v.body v.body_isConj,
    RelTerm.constants]

/- Closed-formula truth is its recursive truth. -/
theorem sentence_satIn_iff_arbitrary
    (φ : Formula D Γ)
    (hSentence : φ.IsSentence)
    (I : Instance D Γ)
    (Q : Set D) :
    RelCalc.Sentence.SatIn
        (⟨φ, hSentence⟩ : Sentence D Γ) I Q ↔
      ∀ σ : Assign D,
        Formula.ArbitraryAssignSatIn Q I σ φ := by
  unfold Sentence.SatIn Formula.SatIn
  rw [hSentence]
  simp [Assign.MapsInto]

end Compile

end Dependency

end RelCalc

------------------------------------------------------------
-- Public Compilation API
------------------------------------------------------------

namespace RelCalc

namespace TGD

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Compile a TGD to a typed QF assertion. -/
def toQFAssert
    (δ : TGD D Γ) : Whiel.QFAssertExpr D Γ :=
  Dependency.Compile.compileTGD δ.1 δ.2

/- Compile a TGD to a no-bound assertion. -/
def toAssertExpr
    (δ : TGD D Γ) : Whiel.AssertExpr D Γ :=
  Whiel.AssertExpr.ofQF δ.toQFAssert

/- Erase a compiled TGD to raw assertion syntax. -/
def toRawAssert
    (δ : TGD D Γ) : Whiel.RawGuard A D :=
  δ.toQFAssert.toRaw

/- Regard a TGD as a RelCalc sentence. -/
def toSentence
    (δ : TGD D Γ) : Sentence D Γ :=
  ⟨δ.1,
    Dependency.Compile.isSentence_of_isTGD δ.1 δ.2⟩

/- A packaged TGD is closed. -/
theorem isSentence
    (δ : TGD D Γ) : δ.1.IsSentence :=
  δ.toSentence.property

/- A packaged TGD has no constants. -/
theorem constants_eq_empty
    (δ : TGD D Γ) : δ.1.constants = ∅ :=
  Dependency.Compile.constants_eq_empty_of_isTGD
    δ.1 δ.2

/- QF compilation preserves active-domain truth. -/
theorem toQFAssert_correct
    (δ : TGD D Γ)
    (I : Instance D Γ) :
    δ.toQFAssert.eval I ↔
      ∀ σ : Assign D,
        Formula.ArbitraryAssignSatIn
          (↑I.Adom : Set D) I σ δ.1 := by
  let v := Dependency.Compile.tgdView δ.1 δ.2
  have hCorrect := v.toQFAssert_correct I
  simpa [toQFAssert,
    Dependency.Compile.compileTGD,
    v, v.formula_eq] using hCorrect

/- Compiled TGD truth is source sentence truth. -/
theorem toAssertExpr_correct
    (δ : TGD D Γ)
    (I : Instance D Γ) :
    δ.toAssertExpr.eval I ↔
      δ.toSentence.SatIn I (↑I.Adom : Set D) := by
  have hAssert :
      δ.toAssertExpr.eval I ↔
        δ.toQFAssert.eval I :=
    Whiel.AssertExpr.ofQF_eval_iff
      δ.toQFAssert I
  have hSentence :
      δ.toSentence.SatIn I (↑I.Adom : Set D) ↔
        ∀ σ : Assign D,
          Formula.ArbitraryAssignSatIn
            (↑I.Adom : Set D) I σ δ.1 :=
    Dependency.Compile.sentence_satIn_iff_arbitrary
      δ.1 δ.toSentence.property I _
  exact hAssert.trans
    ((δ.toQFAssert_correct I).trans hSentence.symm)

/- Checking erasure recovers the compiled TGD guard. -/
@[simp] theorem toRawAssert_toGuard?
    (δ : TGD D Γ) :
    δ.toRawAssert.toGuard? Γ =
      some δ.toQFAssert :=
  Whiel.Guard.toRaw_toGuard? δ.toQFAssert

/- Raw equality proves equality with QF notation. -/
theorem toAssertExpr_eq_of_raw
    (δ : TGD D Γ)
    {G : Whiel.QFAssertExpr D Γ}
    (hRaw : δ.toRawAssert = G.toRaw) :
    δ.toAssertExpr =
      Whiel.AssertExpr.ofQF G := by
  have hGuard : δ.toQFAssert = G :=
    Whiel.Guard.eq_of_toRaw_eq hRaw
  rw [toAssertExpr, hGuard]

/- Compile a TGD list with surface association. -/
def listToQFAssert
    (δs : List (TGD D Γ)) : Whiel.QFAssertExpr D Γ :=
  Whiel.QFAssertExpr.andList (δs.map toQFAssert)

/- Compile a TGD list to a no-bound assertion. -/
def listToAssertExpr
    (δs : List (TGD D Γ)) : Whiel.AssertExpr D Γ :=
  Whiel.AssertExpr.ofQF
    (listToQFAssert δs)

/- Erase a compiled TGD list. -/
def listToRawAssert
    (δs : List (TGD D Γ)) : Whiel.RawGuard A D :=
  (listToQFAssert δs).toRaw

/- Checking list erasure recovers the compiled guard. -/
@[simp] theorem listToRawAssert_toGuard?
    (δs : List (TGD D Γ)) :
    (listToRawAssert δs).toGuard? Γ =
      some (listToQFAssert δs) :=
  Whiel.Guard.toRaw_toGuard? (listToQFAssert δs)

/- Raw equality proves equality for a TGD list. -/
theorem listToAssertExpr_eq_of_raw
    (δs : List (TGD D Γ))
    {G : Whiel.QFAssertExpr D Γ}
    (hRaw : listToRawAssert δs = G.toRaw) :
    listToAssertExpr δs =
      Whiel.AssertExpr.ofQF G := by
  have hGuard : listToQFAssert δs = G :=
    Whiel.Guard.eq_of_toRaw_eq hRaw
  rw [listToAssertExpr, hGuard]

/- TGD-list compilation is pointwise correct. -/
theorem listToQFAssert_correct
    (δs : List (TGD D Γ))
    (I : Instance D Γ) :
    (listToQFAssert δs).eval I ↔
      ∀ δ ∈ δs,
        δ.toSentence.SatIn I (↑I.Adom : Set D) := by
  rw [listToQFAssert,
    Whiel.QFAssertExpr.andList_eval_iff]
  constructor
  · intro h δ hδ
    apply (Dependency.Compile.sentence_satIn_iff_arbitrary
      δ.1 δ.toSentence.property I _).2
    apply (δ.toQFAssert_correct I).1
    exact h δ.toQFAssert
      (List.mem_map.mpr ⟨δ, hδ, rfl⟩)
  · intro h G hG
    rcases List.mem_map.mp hG with ⟨δ, hδ, rfl⟩
    apply (δ.toQFAssert_correct I).2
    exact (Dependency.Compile.sentence_satIn_iff_arbitrary
      δ.1 δ.toSentence.property I _).1 (h δ hδ)

/- Full TGD-list compilation is correct. -/
theorem listToAssertExpr_correct
    (δs : List (TGD D Γ))
    (I : Instance D Γ) :
    (listToAssertExpr δs).eval I ↔
      ∀ δ ∈ δs,
        δ.toSentence.SatIn I (↑I.Adom : Set D) := by
  exact (Whiel.AssertExpr.ofQF_eval_iff
    (listToQFAssert δs) I).trans
      (listToQFAssert_correct δs I)

end TGD

namespace EGD

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Compile an EGD to a typed QF assertion. -/
def toQFAssert
    (δ : EGD D Γ) : Whiel.QFAssertExpr D Γ :=
  Dependency.Compile.compileEGD δ.1 δ.2

/- Compile an EGD to a no-bound assertion. -/
def toAssertExpr
    (δ : EGD D Γ) : Whiel.AssertExpr D Γ :=
  Whiel.AssertExpr.ofQF δ.toQFAssert

/- Erase a compiled EGD to raw assertion syntax. -/
def toRawAssert
    (δ : EGD D Γ) : Whiel.RawGuard A D :=
  δ.toQFAssert.toRaw

/- Regard an EGD as a RelCalc sentence. -/
def toSentence
    (δ : EGD D Γ) : Sentence D Γ :=
  ⟨δ.1,
    Dependency.Compile.isSentence_of_isEGD δ.1 δ.2⟩

/- A packaged EGD is closed. -/
theorem isSentence
    (δ : EGD D Γ) : δ.1.IsSentence :=
  δ.toSentence.property

/- A packaged EGD has no constants. -/
theorem constants_eq_empty
    (δ : EGD D Γ) : δ.1.constants = ∅ :=
  Dependency.Compile.constants_eq_empty_of_isEGD
    δ.1 δ.2

/- QF compilation preserves active-domain truth. -/
theorem toQFAssert_correct
    (δ : EGD D Γ)
    (I : Instance D Γ) :
    δ.toQFAssert.eval I ↔
      ∀ σ : Assign D,
        Formula.ArbitraryAssignSatIn
          (↑I.Adom : Set D) I σ δ.1 := by
  let v := Dependency.Compile.egdView δ.1 δ.2
  have hCorrect := v.toQFAssert_correct I
  simpa [toQFAssert,
    Dependency.Compile.compileEGD,
    v, v.formula_eq] using hCorrect

/- Compiled EGD truth is source sentence truth. -/
theorem toAssertExpr_correct
    (δ : EGD D Γ)
    (I : Instance D Γ) :
    δ.toAssertExpr.eval I ↔
      δ.toSentence.SatIn I (↑I.Adom : Set D) := by
  have hAssert :
      δ.toAssertExpr.eval I ↔
        δ.toQFAssert.eval I :=
    Whiel.AssertExpr.ofQF_eval_iff
      δ.toQFAssert I
  have hSentence :
      δ.toSentence.SatIn I (↑I.Adom : Set D) ↔
        ∀ σ : Assign D,
          Formula.ArbitraryAssignSatIn
            (↑I.Adom : Set D) I σ δ.1 :=
    Dependency.Compile.sentence_satIn_iff_arbitrary
      δ.1 δ.toSentence.property I _
  exact hAssert.trans
    ((δ.toQFAssert_correct I).trans hSentence.symm)

/- Checking erasure recovers the compiled EGD guard. -/
@[simp] theorem toRawAssert_toGuard?
    (δ : EGD D Γ) :
    δ.toRawAssert.toGuard? Γ =
      some δ.toQFAssert :=
  Whiel.Guard.toRaw_toGuard? δ.toQFAssert

/- Raw equality proves equality with QF notation. -/
theorem toAssertExpr_eq_of_raw
    (δ : EGD D Γ)
    {G : Whiel.QFAssertExpr D Γ}
    (hRaw : δ.toRawAssert = G.toRaw) :
    δ.toAssertExpr =
      Whiel.AssertExpr.ofQF G := by
  have hGuard : δ.toQFAssert = G :=
    Whiel.Guard.eq_of_toRaw_eq hRaw
  rw [toAssertExpr, hGuard]

/- Compile an EGD list with surface association. -/
def listToQFAssert
    (δs : List (EGD D Γ)) : Whiel.QFAssertExpr D Γ :=
  Whiel.QFAssertExpr.andList (δs.map toQFAssert)

/- Compile an EGD list to a no-bound assertion. -/
def listToAssertExpr
    (δs : List (EGD D Γ)) : Whiel.AssertExpr D Γ :=
  Whiel.AssertExpr.ofQF
    (listToQFAssert δs)

/- Erase a compiled EGD list. -/
def listToRawAssert
    (δs : List (EGD D Γ)) : Whiel.RawGuard A D :=
  (listToQFAssert δs).toRaw

/- Checking list erasure recovers the compiled guard. -/
@[simp] theorem listToRawAssert_toGuard?
    (δs : List (EGD D Γ)) :
    (listToRawAssert δs).toGuard? Γ =
      some (listToQFAssert δs) :=
  Whiel.Guard.toRaw_toGuard? (listToQFAssert δs)

/- Raw equality proves equality for an EGD list. -/
theorem listToAssertExpr_eq_of_raw
    (δs : List (EGD D Γ))
    {G : Whiel.QFAssertExpr D Γ}
    (hRaw : listToRawAssert δs = G.toRaw) :
    listToAssertExpr δs =
      Whiel.AssertExpr.ofQF G := by
  have hGuard : listToQFAssert δs = G :=
    Whiel.Guard.eq_of_toRaw_eq hRaw
  rw [listToAssertExpr, hGuard]

/- EGD-list compilation is pointwise correct. -/
theorem listToQFAssert_correct
    (δs : List (EGD D Γ))
    (I : Instance D Γ) :
    (listToQFAssert δs).eval I ↔
      ∀ δ ∈ δs,
        δ.toSentence.SatIn I (↑I.Adom : Set D) := by
  rw [listToQFAssert,
    Whiel.QFAssertExpr.andList_eval_iff]
  constructor
  · intro h δ hδ
    apply (Dependency.Compile.sentence_satIn_iff_arbitrary
      δ.1 δ.toSentence.property I _).2
    apply (δ.toQFAssert_correct I).1
    exact h δ.toQFAssert
      (List.mem_map.mpr ⟨δ, hδ, rfl⟩)
  · intro h G hG
    rcases List.mem_map.mp hG with ⟨δ, hδ, rfl⟩
    apply (δ.toQFAssert_correct I).2
    exact (Dependency.Compile.sentence_satIn_iff_arbitrary
      δ.1 δ.toSentence.property I _).1 (h δ hδ)

/- Full EGD-list compilation is correct. -/
theorem listToAssertExpr_correct
    (δs : List (EGD D Γ))
    (I : Instance D Γ) :
    (listToAssertExpr δs).eval I ↔
      ∀ δ ∈ δs,
        δ.toSentence.SatIn I (↑I.Adom : Set D) := by
  exact (Whiel.AssertExpr.ofQF_eval_iff
    (listToQFAssert δs) I).trans
      (listToQFAssert_correct δs I)

end EGD

end RelCalc
