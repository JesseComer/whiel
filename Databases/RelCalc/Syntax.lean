-- Author: Jesse Comer
import Databases.UnnamedModel.RelAtom
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Basic

/-
  Relational calculus syntax.

  Key declarations defined here are `Formula`, `Sentence`,
  `Query`, and `SentenceEntailment`.

  Relational calculus uses the shared `RelTerm` and
  `RelAtom` declarations from `DBLib.UnnamedModel.RelAtom`.
-/

------------------------------------------------------------
-- Relational Calculus Syntax
------------------------------------------------------------

namespace RelCalc

/- Schema-indexed relational-calculus formulas. -/
inductive Formula
    {A : Type}
    [RelationNames A]
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A) : Type where
  | top : Formula D Γ
  | bot : Formula D Γ
  | eq : RelTerm D → RelTerm D → Formula D Γ
  | rel : RelAtom D Γ → Formula D Γ
  | and : Formula D Γ →
      Formula D Γ → Formula D Γ
  | or : Formula D Γ →
      Formula D Γ → Formula D Γ
  | not : Formula D Γ → Formula D Γ
  | imp : Formula D Γ →
      Formula D Γ → Formula D Γ
  | iff : Formula D Γ →
      Formula D Γ → Formula D Γ
  | forall_ : Var → Formula D Γ →
      Formula D Γ
  | exists_ : Var → Formula D Γ →
      Formula D Γ
deriving Repr

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Existentially quantify a list of variables. -/
def existsMany
    (xs : List Var)
    (φ : Formula D Γ) :
    Formula D Γ :=
  xs.foldr Formula.exists_ φ

/- Universally quantify a list of variables. -/
def forallMany
    (xs : List Var)
    (φ : Formula D Γ) :
    Formula D Γ :=
  xs.foldr Formula.forall_ φ

/- FinRelation names in a formula. -/
def relNames : Formula D Γ → Finset A
| .top => ∅
| .bot => ∅
| .eq _ _ => ∅
| .rel a => {a.rel.1}
| .and φ ψ => relNames φ ∪ relNames ψ
| .or φ ψ => relNames φ ∪ relNames ψ
| .not φ => relNames φ
| .imp φ ψ => relNames φ ∪ relNames ψ
| .iff φ ψ => relNames φ ∪ relNames ψ
| .forall_ _ φ => relNames φ
| .exists_ _ φ => relNames φ

/- Free variables in a formula. -/
def freeVars : Formula D Γ → Finset Var
| .top => ∅
| .bot => ∅
| .eq t1 t2 => RelTerm.vars t1 ∪ RelTerm.vars t2
| .rel a => a.vars
| .and φ ψ => freeVars φ ∪ freeVars ψ
| .or φ ψ => freeVars φ ∪ freeVars ψ
| .not φ => freeVars φ
| .imp φ ψ => freeVars φ ∪ freeVars ψ
| .iff φ ψ => freeVars φ ∪ freeVars ψ
| .forall_ x φ => (freeVars φ).erase x
| .exists_ x φ => (freeVars φ).erase x

/- Variables that occur free or bound in a formula. -/
def allVars : Formula D Γ → Finset Var
| .top => ∅
| .bot => ∅
| .eq t u => t.vars ∪ u.vars
| .rel a => a.vars
| .and φ ψ => φ.allVars ∪ ψ.allVars
| .or φ ψ => φ.allVars ∪ ψ.allVars
| .not φ => φ.allVars
| .imp φ ψ => φ.allVars ∪ ψ.allVars
| .iff φ ψ => φ.allVars ∪ ψ.allVars
| .forall_ x φ => insert x φ.allVars
| .exists_ x φ => insert x φ.allVars

/- Variables that occur free or bound as a list. -/
def allVarList : Formula D Γ → List Var
| .top => []
| .bot => []
| .eq t u => t.varList ++ u.varList
| .rel a => RelTerm.tupleVarList a.args
| .and φ ψ => allVarList φ ++ allVarList ψ
| .or φ ψ => allVarList φ ++ allVarList ψ
| .not φ => allVarList φ
| .imp φ ψ => allVarList φ ++ allVarList ψ
| .iff φ ψ => allVarList φ ++ allVarList ψ
| .forall_ x φ => x :: allVarList φ
| .exists_ x φ => x :: allVarList φ

/- Largest natural number in a list, defaulting to zero. -/
private def maxVarList : List Var → Nat
| [] => 0
| x :: xs => max x (maxVarList xs)

/- Members of `maxVarList` are bounded by it. -/
private theorem mem_maxVarList_le :
    ∀ {xs : List Var}
      {x : Var},
      x ∈ xs → x ≤ maxVarList xs
| [], _, hx =>
    by cases hx
| y :: ys, x, hx =>
    by
      have hcases : x = y ∨ x ∈ ys := by
        simpa using hx
      rcases hcases with hxy | hxTail
      · subst x
        exact le_max_left y (maxVarList ys)
      · exact le_max_of_le_right
          (mem_maxVarList_le hxTail)

/- Largest variable occurring free or bound in a formula. -/
def maxVar
    (φ : Formula D Γ) :
    Nat :=
  maxVarList φ.allVarList

/- Term variable membership implies list membership. -/
private theorem mem_relTermVarList_of_mem_vars
    {t : RelTerm D}
    {x : Var}
    (hx : x ∈ t.vars) :
    x ∈ RelTerm.varList t := by
  cases t with
  | var y =>
      simpa [RelTerm.vars, RelTerm.varList] using hx
  | const _ =>
      simp [RelTerm.vars] at hx

/- Term-list variable membership implies list membership. -/
private theorem mem_relTermListVarList_of_mem_listVars :
    ∀ {ts : List (RelTerm D)}
      {x : Var},
      x ∈ RelTerm.listVars ts →
        x ∈ RelTerm.listVarList ts
| [], _, hx =>
    by simp [RelTerm.listVars] at hx
| t :: ts, x, hx =>
    by
      rcases Finset.mem_union.mp
          (by simpa [RelTerm.listVars] using hx) with
        hxT | hxTs
      · exact List.mem_append.mpr
          (Or.inl (mem_relTermVarList_of_mem_vars hxT))
      · exact List.mem_append.mpr
          (Or.inr
            (mem_relTermListVarList_of_mem_listVars hxTs))

/-
  Term-tuple variable membership implies list membership.
-/
private theorem mem_relTermTupleVarList_of_mem_tupleVars
    {n : Nat}
    {ts : Vector (RelTerm D) n}
    {x : Var}
    (hx : x ∈ RelTerm.tupleVars ts) :
    x ∈ RelTerm.tupleVarList ts :=
  mem_relTermListVarList_of_mem_listVars hx

/- `allVars` membership implies `allVarList` membership. -/
theorem mem_allVarList_of_mem_allVars
    {φ : Formula D Γ}
    {x : Var}
    (hx : x ∈ φ.allVars) :
    x ∈ φ.allVarList := by
  induction φ with
  | top =>
      simp [allVars] at hx
  | bot =>
      simp [allVars] at hx
  | eq t u =>
      rcases Finset.mem_union.mp
          (by simpa [allVars] using hx) with hxT | hxU
      · exact List.mem_append.mpr
          (Or.inl (mem_relTermVarList_of_mem_vars hxT))
      · exact List.mem_append.mpr
          (Or.inr (mem_relTermVarList_of_mem_vars hxU))
  | rel a =>
      exact mem_relTermTupleVarList_of_mem_tupleVars
        (by simpa [allVars, RelAtom.vars] using hx)
  | and φ ψ ihφ ihψ =>
      rcases Finset.mem_union.mp
          (by simpa [allVars] using hx) with hxφ | hxψ
      · exact List.mem_append.mpr (Or.inl (ihφ hxφ))
      · exact List.mem_append.mpr (Or.inr (ihψ hxψ))
  | or φ ψ ihφ ihψ =>
      rcases Finset.mem_union.mp
          (by simpa [allVars] using hx) with hxφ | hxψ
      · exact List.mem_append.mpr (Or.inl (ihφ hxφ))
      · exact List.mem_append.mpr (Or.inr (ihψ hxψ))
  | not φ ih =>
      simpa [allVars, allVarList] using ih hx
  | imp φ ψ ihφ ihψ =>
      rcases Finset.mem_union.mp
          (by simpa [allVars] using hx) with hxφ | hxψ
      · exact List.mem_append.mpr (Or.inl (ihφ hxφ))
      · exact List.mem_append.mpr (Or.inr (ihψ hxψ))
  | iff φ ψ ihφ ihψ =>
      rcases Finset.mem_union.mp
          (by simpa [allVars] using hx) with hxφ | hxψ
      · exact List.mem_append.mpr (Or.inl (ihφ hxφ))
      · exact List.mem_append.mpr (Or.inr (ihψ hxψ))
  | forall_ y φ ih =>
      rcases Finset.mem_insert.mp
          (by simpa [allVars] using hx) with hxy | hxφ
      · exact List.mem_cons.mpr (Or.inl hxy)
      · exact List.mem_cons.mpr (Or.inr (ih hxφ))
  | exists_ y φ ih =>
      rcases Finset.mem_insert.mp
          (by simpa [allVars] using hx) with hxy | hxφ
      · exact List.mem_cons.mpr (Or.inl hxy)
      · exact List.mem_cons.mpr (Or.inr (ih hxφ))

/- Free variables also occur in `allVars`. -/
theorem freeVars_subset_allVars
    (φ : Formula D Γ) :
    φ.freeVars ⊆ φ.allVars := by
  induction φ with
  | top =>
      intro x hx
      simp [freeVars] at hx
  | bot =>
      intro x hx
      simp [freeVars] at hx
  | eq t u =>
      intro x hx
      simpa [freeVars, allVars] using hx
  | rel a =>
      intro x hx
      simpa [freeVars, allVars] using hx
  | and φ ψ ihφ ihψ =>
      intro x hx
      rcases Finset.mem_union.mp
          (by simpa [freeVars] using hx) with hxφ | hxψ
      · exact Finset.mem_union.mpr
          (Or.inl (ihφ hxφ))
      · exact Finset.mem_union.mpr
          (Or.inr (ihψ hxψ))
  | or φ ψ ihφ ihψ =>
      intro x hx
      rcases Finset.mem_union.mp
          (by simpa [freeVars] using hx) with hxφ | hxψ
      · exact Finset.mem_union.mpr
          (Or.inl (ihφ hxφ))
      · exact Finset.mem_union.mpr
          (Or.inr (ihψ hxψ))
  | not φ ih =>
      intro x hx
      simpa [freeVars, allVars] using ih hx
  | imp φ ψ ihφ ihψ =>
      intro x hx
      rcases Finset.mem_union.mp
          (by simpa [freeVars] using hx) with hxφ | hxψ
      · exact Finset.mem_union.mpr
          (Or.inl (ihφ hxφ))
      · exact Finset.mem_union.mpr
          (Or.inr (ihψ hxψ))
  | iff φ ψ ihφ ihψ =>
      intro x hx
      rcases Finset.mem_union.mp
          (by simpa [freeVars] using hx) with hxφ | hxψ
      · exact Finset.mem_union.mpr
          (Or.inl (ihφ hxφ))
      · exact Finset.mem_union.mpr
          (Or.inr (ihψ hxψ))
  | forall_ y φ ih =>
      intro x hx
      exact Finset.mem_insert_of_mem
        (ih ((Finset.mem_erase.mp hx).2))
  | exists_ y φ ih =>
      intro x hx
      exact Finset.mem_insert_of_mem
        (ih ((Finset.mem_erase.mp hx).2))

/- Formula variables are bounded by `maxVar`. -/
theorem mem_allVars_le_maxVar
    {φ : Formula D Γ}
    {x : Var}
    (hx : x ∈ φ.allVars) :
    x ≤ φ.maxVar := by
  exact mem_maxVarList_le
    (mem_allVarList_of_mem_allVars hx)

/- Formula variables are strictly below `maxVar + 1`. -/
theorem mem_allVars_lt_maxVar_succ
    {φ : Formula D Γ}
    {x : Var}
    (hx : x ∈ φ.allVars) :
    x < φ.maxVar + 1 :=
  Nat.lt_succ_of_le (mem_allVars_le_maxVar hx)

/- Constants occurring in a formula. -/
def constants : Formula D Γ → Finset D
| .top => ∅
| .bot => ∅
| .eq t1 t2 =>
    RelTerm.constants t1 ∪ RelTerm.constants t2
| .rel a => a.constants
| .and φ ψ => constants φ ∪ constants ψ
| .or φ ψ => constants φ ∪ constants ψ
| .not φ => constants φ
| .imp φ ψ => constants φ ∪ constants ψ
| .iff φ ψ => constants φ ∪ constants ψ
| .forall_ _ φ => constants φ
| .exists_ _ φ => constants φ

/- A formula is a sentence when it has no free variables. -/
def IsSentence
    (φ : Formula D Γ) : Prop :=
  φ.freeVars = ∅

instance
    (φ : Formula D Γ) :
    Decidable φ.IsSentence := by
  unfold IsSentence
  infer_instance

theorem freeVars_existsMany
    (xs : List Var)
    (φ : Formula D Γ) :
    (existsMany xs φ).freeVars =
      xs.foldr (fun x S => S.erase x) φ.freeVars := by
  induction xs generalizing φ with
  | nil =>
      simp [existsMany]
  | cons x xs ih =>
      have ih' :
          (List.foldr Formula.exists_ φ xs).freeVars =
            xs.foldr
              (fun y S => S.erase y)
              φ.freeVars := by
        simpa [existsMany] using ih φ
      simp [existsMany, freeVars]
      simpa using congrArg
        (fun S : Finset Var => S.erase x) ih'

theorem constants_existsMany
    (xs : List Var)
    (φ : Formula D Γ) :
    (existsMany xs φ).constants = φ.constants := by
  induction xs generalizing φ with
  | nil =>
      simp [existsMany]
  | cons x xs ih =>
      simpa [existsMany, constants] using ih φ

theorem freeVars_forallMany
    (xs : List Var)
    (φ : Formula D Γ) :
    (forallMany xs φ).freeVars =
      xs.foldr (fun x S => S.erase x) φ.freeVars := by
  induction xs generalizing φ with
  | nil =>
      simp [forallMany]
  | cons x xs ih =>
      have ih' :
          (List.foldr Formula.forall_ φ xs).freeVars =
            xs.foldr
              (fun y S => S.erase y)
              φ.freeVars := by
        simpa [forallMany] using ih φ
      simp [forallMany, freeVars]
      simpa using congrArg
        (fun S : Finset Var => S.erase x) ih'

theorem constants_forallMany
    (xs : List Var)
    (φ : Formula D Γ) :
    (forallMany xs φ).constants = φ.constants := by
  induction xs generalizing φ with
  | nil =>
      simp [forallMany]
  | cons x xs ih =>
      simpa [forallMany, constants] using ih φ

end Formula

end RelCalc

------------------------------------------------------------
-- Relational Calculus Sentences
------------------------------------------------------------

namespace RelCalc

/-
  RelCalc sentences are the closed-formula fragment.
-/
abbrev Sentence
    {A : Type}
    {_ : RelationNames A}
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  {φ : Formula D Γ // φ.IsSentence}

namespace Sentence

variable {A D : Type}
variable [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/- Constants occurring in a sentence. -/
def constants
    (φ : Sentence D Γ) : Finset D :=
  φ.1.constants

end Sentence

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Package a closed formula as a sentence. -/
def toSentence
    (φ : Formula D Γ)
    (h : φ.IsSentence) :
    Sentence D Γ :=
  ⟨φ, h⟩

end Formula

end RelCalc

------------------------------------------------------------
-- Relational Calculus Queries
------------------------------------------------------------

namespace RelCalc

/-
  A query packages a well-formed formula with an ordered
  output variable vector whose length is the query's arity
  index and whose underlying set is exactly the set of free
  variables.
-/
structure Query
    {A : Type}
    {_ : RelationNames A}
    (D : Type)
    [Domain D]
    (Γ : UnnamedSchema A)
    (n : Nat) where
  vars : Vector Var n
  form : Formula D Γ
  freeVars_eq : form.freeVars = vars.toList.toFinset

namespace Query

variable {A D : Type}
variable [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}
variable {n : Nat}

instance : CoeOut (Query D Γ n) (Formula D Γ) where
  coe q := q.form

/- Output arity of a query. -/
abbrev arity
    (_ : Query D Γ n) : Nat :=
  n

/- FinRelation names in a query. -/
def relNames
    (q : Query D Γ n) : Finset A :=
  q.form.relNames

/- Free variables in a query. -/
def freeVars
    (q : Query D Γ n) : Finset Var :=
  q.form.freeVars

/- Constants occurring in a query. -/
def constants
    (q : Query D Γ n) : Finset D :=
  q.form.constants

end Query

end RelCalc

------------------------------------------------------------
-- Relational Calculus Entailments
------------------------------------------------------------

namespace RelCalc

structure SentenceEntailment
    {A D : Type}
    [RelationNames A]
    [Domain D]
    (Γ : UnnamedSchema A) where
  axioms : List (RelCalc.Sentence D Γ)
  conjecture : RelCalc.Sentence D Γ

namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Constants occurring in a list of sentences. -/
def sentenceListConstants :
    List (RelCalc.Sentence D Γ) → Finset D
| [] => ∅
| φ :: φs => φ.constants ∪ sentenceListConstants φs

/- All constants occurring in an entailment. -/
def constants
    (E : SentenceEntailment (D := D) Γ) : Finset D :=
  sentenceListConstants E.axioms ∪ E.conjecture.constants

/-
  Constants of a member sentence occur in list constants.
-/
private lemma constants_subset_sentenceListConstants
    {φ : RelCalc.Sentence D Γ}
    {φs : List (RelCalc.Sentence D Γ)}
    (hφ : φ ∈ φs) :
    φ.constants ⊆ sentenceListConstants φs := by
  induction φs with
  | nil =>
      cases hφ
  | cons ψ ψs ih =>
      have hcases : φ = ψ ∨ φ ∈ ψs := by
        simpa using hφ
      intro d hd
      unfold sentenceListConstants
      exact Finset.mem_union.mpr <| by
        cases hcases with
        | inl h =>
            subst h
            exact Or.inl hd
        | inr h =>
            exact Or.inr (ih h hd)

/- Constants of an axiom occur in entailment constants. -/
lemma axiom_constants
    (E : SentenceEntailment (D := D) Γ)
    {φ : RelCalc.Sentence D Γ}
    (hφ : φ ∈ E.axioms) :
    φ.constants ⊆ E.constants := by
  intro d hd
  exact Finset.mem_union.mpr
    (Or.inl
      (constants_subset_sentenceListConstants
        (φ := φ) (φs := E.axioms) hφ hd))

/-
  Constants of the conjecture occur in entailment
  constants.
-/
lemma conjecture_constants
    (E : SentenceEntailment (D := D) Γ) :
    E.conjecture.constants ⊆ E.constants := by
  intro d hd
  exact Finset.mem_union.mpr (Or.inr hd)

end SentenceEntailment

end RelCalc
