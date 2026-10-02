-- Author: Jesse Comer
import Databases.Datalog.Syntax
import Databases.UnnamedModel.RelAtom

/-
  This file specifies the semantics of Datalog rules; that
  is, what it means for an instance to satisfy a rule body
  under some variable assignment.

  This file uses the shared `Assign`, `RelTerm.eval`,
  `RelAtom.evalTuple`, and `RelAtom.Sat` declarations from
  `DBLib.UnnamedModel.RelAtom`.

  Key declarations defined here are:
    * `Atom.Sat`
    * `Body.Satisfied`
    * `Body.satisfied_mono`
    * `Rule.bodySatisfied`
    * `Rule.headSatisfied`

  These definitions give the ordinary reading of a rule as
  body satisfaction implying head satisfaction. The support
  lemmas record assignment congruence and monotonicity in
  the interpreted relations.
-/

------------------------------------------------------------
-- Datalog Atom and Body Satisfaction
------------------------------------------------------------

namespace Datalog

namespace Atom

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Atom satisfaction in an instance. -/
def Sat
    (I : Instance D Γ)
    (σ : Assign D) :
    Atom D Γ → Prop
| .rel a => a.Sat I σ
| .eq lhs rhs => lhs.eval σ = rhs.eval σ

instance
    (I : Instance D Γ)
    (σ : Assign D)
    (b : Atom D Γ) :
    Decidable (b.Sat I σ) := by
  cases b with
  | rel a =>
      unfold Sat
      infer_instance
  | eq lhs rhs =>
      unfold Sat
      infer_instance

end Atom

namespace Body

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Satisfaction of a finite rule body. -/
def Satisfied :
    List (Atom D Γ) → Instance D Γ → Assign D → Prop
| [], _, _ => True
| b :: body, I, σ => b.Sat I σ ∧ Satisfied body I σ

instance
    (body : List (Atom D Γ))
    (I : Instance D Γ)
    (σ : Assign D) :
    Decidable (Satisfied body I σ) := by
  induction body with
  | nil =>
      exact isTrue trivial
  | cons a body ih =>
      unfold Satisfied
      exact instDecidableAnd

end Body

end Datalog

------------------------------------------------------------
-- Rule Satisfaction
------------------------------------------------------------

namespace Datalog

namespace Rule

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Satisfaction of all atoms in a rule body. -/
def bodySatisfied
    (r : Rule D Γ)
    (J : Instance D Γ)
    (σ : Assign D) : Prop :=
  Body.Satisfied r.body J σ

instance
    (r : Rule D Γ)
    (J : Instance D Γ)
    (σ : Assign D) :
    Decidable (r.bodySatisfied J σ) := by
  unfold bodySatisfied
  infer_instance

/-
  Satisfaction of a rule head in a program-schema
  instance.
-/
def headSatisfied
    (r : Rule D Γ)
    (J : Instance D Γ)
    (σ : Assign D) : Prop :=
  r.head.Sat J σ

instance
    (r : Rule D Γ)
    (J : Instance D Γ)
    (σ : Assign D) :
    Decidable (r.headSatisfied J σ) := by
  unfold headSatisfied
  infer_instance

end Rule

end Datalog

------------------------------------------------------------
-- Satisfaction Congruence And Monotonicity
------------------------------------------------------------

namespace Datalog

namespace Atom

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Atom satisfaction depends only on variables in the atom. -/
private theorem sat_congr_assign
    (b : Atom D Γ)
    (I : Instance D Γ)
    {σ₁ σ₂ : Assign D}
    (hσ :
      ∀ x : Var,
        x ∈ b.varList → σ₁ x = σ₂ x) :
    b.Sat I σ₁ → b.Sat I σ₂ := by
  cases b with
  | rel a =>
      intro hSat
      have hEval :
          a.evalTuple σ₁ = a.evalTuple σ₂ :=
        a.evalTuple_eq_of_assign_eq_on_vars hσ
      simpa [Atom.Sat, RelAtom.Sat, RelAtom.evalFact,
        RelFact.Mem, hEval] using hSat
  | eq lhs rhs =>
      intro hSat
      have hL :
          lhs.eval σ₁ = lhs.eval σ₂ :=
        lhs.eval_eq_of_assign_eq_on_var?
          (fun x hx => by
            have hxMem :
                x ∈ [lhs, rhs].filterMap RelTerm.var? :=
              List.mem_filterMap.mpr
                ⟨lhs, by simp, hx⟩
            exact hσ x (by simpa [Atom.varList] using hxMem))
      have hR :
          rhs.eval σ₁ = rhs.eval σ₂ :=
        rhs.eval_eq_of_assign_eq_on_var?
          (fun x hx => by
            have hxMem :
                x ∈ [lhs, rhs].filterMap RelTerm.var? :=
              List.mem_filterMap.mpr
                ⟨rhs, by simp, hx⟩
            exact hσ x (by simpa [Atom.varList] using hxMem))
      simpa [Atom.Sat, hL, hR] using hSat

end Atom

namespace Body

/-
  Extract satisfaction of a listed atom from body
  satisfaction.
-/
theorem sat_of_satisfied
    {A D : Type} [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (σ : Assign D)
    {b : Atom D Γ} :
    ∀ body : List (Atom D Γ),
      b ∈ body →
        Body.Satisfied body I σ →
          b.Sat I σ
| [], hMem, _ => by
    cases hMem
| b :: body, hMem, hBody =>
    match List.mem_cons.mp hMem with
    | Or.inl hEq => by
        subst hEq
        exact hBody.1
    | Or.inr hRest =>
        sat_of_satisfied I σ body hRest hBody.2

/-
  Body satisfaction depends only on variables occurring in
  atoms.
-/
private theorem satisfied_congr_assign
    {A D : Type} [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    {σ₁ σ₂ : Assign D} :
    ∀ body : List (Atom D Γ),
      (∀ (b : Atom D Γ) (x : Var),
        b ∈ body →
          x ∈ b.varList →
            σ₁ x = σ₂ x) →
        Body.Satisfied body I σ₁ →
          Body.Satisfied body I σ₂
| [], _hσ, _hBody => trivial
| b :: body, hσ, hBody =>
    ⟨b.sat_congr_assign I
        (fun x hx => hσ b x List.mem_cons_self hx)
        hBody.1,
      satisfied_congr_assign I body
        (fun c x hc hx =>
          hσ c x (List.mem_cons_of_mem _ hc) hx)
        hBody.2⟩

/-
  Body satisfaction is monotone in the interpreted
  relations.
-/
theorem satisfied_mono
    {A D : Type}
    [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    {I J : Instance D Γ}
    {σ : Assign D}
    (hSub : Instance.Subset I J) :
    ∀ body : List (Atom D Γ),
      Body.Satisfied body I σ →
        Body.Satisfied body J σ
| [], _ => trivial
| b :: body, hBody => by
    cases b with
    | rel a =>
        exact
          ⟨hSub a.rel hBody.1,
            satisfied_mono hSub body hBody.2⟩
    | eq lhs rhs =>
        exact
          ⟨hBody.1, satisfied_mono hSub body hBody.2⟩

end Body

namespace Rule

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Rule-body satisfaction depends only on variables occurring
  in the rule.
-/
theorem bodySatisfied_congr_assign
    (r : Rule D Γ)
    (J : Instance D Γ)
    {σ₁ σ₂ : Assign D}
    (hσ :
      ∀ x : Var,
        x ∈ r.varList → σ₁ x = σ₂ x)
    (hBody : r.bodySatisfied J σ₁) :
    r.bodySatisfied J σ₂ := by
  unfold Rule.bodySatisfied at hBody ⊢
  exact
    Body.satisfied_congr_assign J r.body
      (fun b x hb hx =>
        hσ x (r.atom_in_body_var_mem_varList hb hx))
      hBody

/-
  Rule-head satisfaction depends only on variables occurring
  in the rule.
-/
theorem headSatisfied_congr_assign
    (r : Rule D Γ)
    (J : Instance D Γ)
    {σ₁ σ₂ : Assign D}
    (hσ :
      ∀ x : Var,
        x ∈ r.varList → σ₁ x = σ₂ x) :
    r.headSatisfied J σ₁ ↔
      r.headSatisfied J σ₂ := by
  have hHead :
      r.head.evalTuple σ₁ = r.head.evalTuple σ₂ :=
    r.head.evalTuple_eq_of_assign_eq_on_vars
      (fun x hx => hσ x (r.head_var_mem_varList hx))
  unfold Rule.headSatisfied RelAtom.Sat RelAtom.evalFact
    RelFact.Mem
  rw [hHead]

end Rule

end Datalog
