-- Author: Jesse Comer
import Databases.FOL.Entailment

/-
  This file defines shallow first-order semantics whose
  relation and function symbols are curried Lean values.

  Key definitions include:
    * `FOL.Shallow.Model`
    * `FOL.Shallow.Sat`
    * `FOL.SentenceEntailment.ShallowValid`
    * `FOL.SentenceEntailment.ImplicationShallowValid`

  A finite structure induces a shallow model over its
  carrier subtype. Correctness is proven by:
    * `FOL.Formula.shallowSat_ofFinStruct_iff_sat`
    * `FOL.SentenceEntailment.valid_of_shallowValid`
-/

------------------------------------------------------------
-- Curried Shallow Models
------------------------------------------------------------

namespace FOL

namespace Shallow

universe v

/- Curried `n`-ary values over one carrier. -/
def Nary
    (ι : Type)
    (β : Sort v) :
    Nat → Sort (imax 1 v)
  | 0 => β
  | n + 1 => ι → Nary ι β n

namespace Nary

/- Apply a curried value to an indexed tuple. -/
def apply
    {ι : Type}
    {β : Sort v} :
    {n : Nat} → Nary ι β n → Tuple ι n → β
  | 0, f, _ => f
  | _ + 1, f, args =>
      apply (f args[0]) (Tuple.tail args)

/- Curry a function on indexed tuples. -/
def curry
    {ι : Type}
    {β : Sort v} :
    {n : Nat} → (Tuple ι n → β) → Nary ι β n
  | 0, f => f Tuple.empty
  | _ + 1, f =>
      fun head =>
        curry fun tail => f (Tuple.cons head tail)

/-
  Applying a curried tuple function recovers the function.
-/
@[simp]
theorem apply_curry
    {ι : Type}
    {β : Sort v}
    {n : Nat}
    (f : Tuple ι n → β)
    (args : Tuple ι n) :
    apply (curry f) args = f args := by
  induction n with
  | zero =>
      change f Tuple.empty = f args
      congr
      apply Vector.ext
      intro i hi
      omega
  | succ n ih =>
      change
        apply
            (curry
              (fun tail =>
                f (Tuple.cons args[0] tail)))
            (Tuple.tail args) =
          f args
      rw [ih, Tuple.cons_tail]

end Nary

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/- A shallow interpretation of one FOL signature. -/
structure Model (ι : Type) where
  rels :
    (X : Signature.Rel Λ) →
      Nary ι Prop (Λ.arity X)
  funcs :
    (f : Signature.Fun Λ) →
      Nary ι ι (Λ.funArity f)

end Shallow

end FOL

------------------------------------------------------------
-- Shallow Satisfaction
------------------------------------------------------------

namespace FOL

namespace Shallow

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/- Update a shallow variable assignment. -/
def update
    {ι : Type}
    (σ : Var → ι)
    (x : Var)
    (d : ι) :
    Var → ι :=
  fun y => if y = x then d else σ y

mutual
/- Evaluate a term in a shallow model. -/
  def evalTerm
      {ι : Type}
      (I : Model (Λ := Λ) ι)
      (σ : Var → ι) :
      Term Λ → ι
    | .var x => σ x
    | .func f args =>
        Nary.apply (I.funcs f)
          (evalTermList I σ args)

/- Evaluate an indexed term list in a shallow model. -/
  def evalTermList
      {ι : Type}
      (I : Model (Λ := Λ) ι)
      (σ : Var → ι) :
      {n : Nat} → TermList Λ n → Tuple ι n
    | _, .nil => Tuple.empty
    | _, .cons t ts =>
        Vector.ofFn
          (fun i =>
            Fin.cases
              (evalTerm I σ t)
              (fun j =>
                (evalTermList I σ ts).get j)
              i)
end

/- Shallow satisfaction under a carrier assignment. -/
def Sat
    {ι : Type}
    (φ : Formula Λ)
    (I : Model (Λ := Λ) ι)
    (σ : Var → ι) : Prop :=
  match φ with
  | .top => True
  | .bot => False
  | .eq t₁ t₂ =>
      evalTerm I σ t₁ = evalTerm I σ t₂
  | .rel X ts =>
      Nary.apply (I.rels X) (evalTermList I σ ts)
  | .and φ ψ => Sat φ I σ ∧ Sat ψ I σ
  | .or φ ψ => Sat φ I σ ∨ Sat ψ I σ
  | .not φ => ¬ Sat φ I σ
  | .imp φ ψ => Sat φ I σ → Sat ψ I σ
  | .iff φ ψ => Sat φ I σ ↔ Sat ψ I σ
  | .forall_ x φ =>
      ∀ d : ι, Sat φ I (update σ x d)
  | .exists_ x φ =>
      ∃ d : ι, Sat φ I (update σ x d)

/- Assignment-independent shallow sentence satisfaction. -/
def SentenceSat
    {ι : Type}
    (φ : FOL.Sentence Λ)
    (I : Model (Λ := Λ) ι) : Prop :=
  ∀ σ : Var → ι, Sat φ.1 I σ

end Shallow

end FOL

------------------------------------------------------------
-- Finite-Structure Interpretation
------------------------------------------------------------

namespace FOL

namespace Shallow

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Λ : Signature A F}

/- Forget carrier proofs in an indexed tuple. -/
def eraseTuple
    {M : FinStruct D Λ}
    {n : Nat}
    (args : Tuple (Elem M) n) :
    Tuple D n :=
  Vector.ofFn (fun i => (args.get i).1)

/- Erasing carrier proofs preserves carrier membership. -/
theorem eraseTuple_isTupleOver
    {M : FinStruct D Λ}
    {n : Nat}
    (args : Tuple (Elem M) n) :
    (eraseTuple args).isTupleOver M.carrier := by
  intro i
  have hGet :
      (eraseTuple args).get i = (args.get i).1 := by
    simp [eraseTuple, Vector.get, Vector.ofFn]
  rw [hGet]
  exact (args.get i).2

/- The shallow model induced by a finite structure. -/
def ofFinStruct
    (M : FinStruct D Λ) :
    Model (Λ := Λ) (Elem M) where
  rels X :=
    Nary.curry fun args =>
      eraseTuple args ∈ M.rels X
  funcs f :=
    Nary.curry fun args =>
      ⟨M.funcs f (eraseTuple args),
        M.funcs_closed f (eraseTuple args)
          (eraseTuple_isTupleOver args)⟩

@[simp]
theorem apply_rels_ofFinStruct
    (M : FinStruct D Λ)
    (X : Signature.Rel Λ)
    (args : Tuple (Elem M) (Λ.arity X)) :
    Nary.apply ((ofFinStruct M).rels X) args ↔
      eraseTuple args ∈ M.rels X := by
  simp [ofFinStruct]

@[simp]
theorem apply_funcs_ofFinStruct_val
    (M : FinStruct D Λ)
    (f : Signature.Fun Λ)
    (args : Tuple (Elem M) (Λ.funArity f)) :
    (Nary.apply ((ofFinStruct M).funcs f) args).1 =
      M.funcs f (eraseTuple args) := by
  simp [ofFinStruct]

mutual
/- Shallow term evaluation has the deep domain value. -/
  @[simp]
  theorem evalTerm_ofFinStruct_val
      (M : FinStruct D Λ)
      (σ : Assign M)
      (t : Term Λ) :
      (evalTerm (ofFinStruct M) σ t).1 =
        Semantics.evalTerm M σ t := by
    cases t with
    | var x => rfl
    | func f args =>
        simp only [evalTerm,
          apply_funcs_ofFinStruct_val,
          Semantics.evalTerm]
        rw [evalTermList_ofFinStruct_erase]

/-
  Shallow term-list evaluation erases to deep evaluation.
-/
  @[simp]
  theorem evalTermList_ofFinStruct_erase
      (M : FinStruct D Λ)
      (σ : Assign M)
      {n : Nat}
      (ts : TermList Λ n) :
      eraseTuple (evalTermList (ofFinStruct M) σ ts) =
        Semantics.evalTermList M σ ts := by
    cases ts with
    | nil =>
        apply Vector.ext
        intro i hi
        omega
    | @cons n t ts =>
        apply Vector.ext
        intro i hi
        cases i with
        | zero =>
            simp [eraseTuple, evalTermList,
              Semantics.evalTermList, Vector.get,
              Vector.ofFn, evalTerm_ofFinStruct_val]
        | succ i =>
            have hi' : i < n :=
              Nat.succ_lt_succ_iff.mp hi
            have hTail :=
              evalTermList_ofFinStruct_erase M σ ts
            have hGet :=
              congrArg
                (fun v : Tuple D n =>
                  v.get ⟨i, hi'⟩) hTail
            simpa [eraseTuple, evalTermList,
              Semantics.evalTermList, Vector.get,
              Vector.ofFn] using hGet
end

end Shallow

end FOL

------------------------------------------------------------
-- Reflection Correctness
------------------------------------------------------------

namespace FOL

namespace Formula

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Λ : Signature A F}

/- Canonical shallow satisfaction is deep satisfaction. -/
theorem shallowSat_ofFinStruct_iff_sat
    (φ : Formula Λ)
    (M : FinStruct D Λ)
    (σ : Assign M) :
    Shallow.Sat φ (Shallow.ofFinStruct M) σ ↔
      φ.Sat M σ := by
  induction φ generalizing σ with
  | top => rfl
  | bot => rfl
  | eq t₁ t₂ =>
      simp [Shallow.Sat, Sat, Subtype.ext_iff]
  | rel X ts =>
      simp only [Shallow.Sat, Sat,
        Shallow.apply_rels_ofFinStruct]
      rw [Shallow.evalTermList_ofFinStruct_erase]
  | and φ ψ hφ hψ =>
      simp [Shallow.Sat, Sat, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [Shallow.Sat, Sat, hφ, hψ]
  | not φ hφ =>
      simp [Shallow.Sat, Sat, hφ]
  | imp φ ψ hφ hψ =>
      simp [Shallow.Sat, Sat, hφ, hψ]
  | iff φ ψ hφ hψ =>
      simp [Shallow.Sat, Sat, hφ, hψ]
  | forall_ x φ hφ =>
      constructor
      · intro h d
        have hBody := (hφ
          (Shallow.update σ x d)).mp (h d)
        simpa only [Shallow.update, Assign.update]
          using hBody
      · intro h d
        apply (hφ (Shallow.update σ x d)).mpr
        simpa only [Shallow.update, Assign.update]
          using h d
  | exists_ x φ hφ =>
      constructor
      · rintro ⟨d, hBody⟩
        refine ⟨d, ?_⟩
        have hSat :=
          (hφ (Shallow.update σ x d)).mp hBody
        simpa only [Shallow.update, Assign.update]
          using hSat
      · rintro ⟨d, hBody⟩
        refine ⟨d, ?_⟩
        apply (hφ (Shallow.update σ x d)).mpr
        simpa only [Shallow.update, Assign.update]
          using hBody

end Formula

namespace Sentence

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Λ : Signature A F}

/- Canonical shallow sentence satisfaction is deep. -/
theorem shallowSat_ofFinStruct_iff_sat
    (φ : FOL.Sentence Λ)
    (M : FinStruct D Λ) :
    Shallow.SentenceSat φ (Shallow.ofFinStruct M) ↔
      φ.Sat M := by
  simp [Shallow.SentenceSat, Sentence.Sat,
    Formula.shallowSat_ofFinStruct_iff_sat]

end Sentence

end FOL

------------------------------------------------------------
-- Shallow Entailment Validity
------------------------------------------------------------

namespace FOL

namespace SentenceEntailment

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Λ : Signature A F}

/- Satisfaction of a canonical axiom conjunction. -/
theorem sentenceSat_conjoin_of_forall_mem
    {ι : Type}
    (I : Shallow.Model (Λ := Λ) ι)
    (φs : List (FOL.Sentence Λ))
    (h : ∀ φ ∈ φs,
      Shallow.SentenceSat φ I) :
    Shallow.SentenceSat (Sentence.conjoin φs) I := by
  intro σ
  induction φs with
  | nil =>
      exact True.intro
  | cons φ φs ih =>
      cases φs with
      | nil =>
          exact h φ (by simp) σ
      | cons ψ ψs =>
          constructor
          · exact h φ (by simp) σ
          · apply ih
            intro χ hχ
            exact h χ (by simp [hχ])

/- Canonical-implication validity in shallow models. -/
def ImplicationShallowValid
    (E : SentenceEntailment Λ) : Prop :=
  ∀ (ι : Type) [Inhabited ι],
    ∀ I : Shallow.Model (Λ := Λ) ι,
      Shallow.SentenceSat E.toImplication I

/- Validity over all inhabited shallow models. -/
def ShallowValid
    (E : SentenceEntailment Λ) : Prop :=
  ∀ (ι : Type) [Inhabited ι],
    ∀ I : Shallow.Model (Λ := Λ) ι,
      (∀ φ ∈ E.axioms,
        Shallow.SentenceSat φ I) →
        Shallow.SentenceSat E.conjecture I

/- A closed implication proof gives shallow validity. -/
theorem shallowValid_of_implicationShallowValid
    (E : SentenceEntailment Λ)
    (h : E.ImplicationShallowValid) :
    E.ShallowValid := by
  intro ι _ I hAxioms σ
  have hAntecedent :=
    sentenceSat_conjoin_of_forall_mem
      I E.axioms hAxioms
  have hImplication := h ι I σ
  change
    Shallow.Sat (Sentence.conjoin E.axioms).1 I σ →
      Shallow.Sat E.conjecture.1 I σ
    at hImplication
  exact hImplication (hAntecedent σ)

/- Shallow validity implies finite-structure validity. -/
theorem valid_of_shallowValid
    (E : SentenceEntailment Λ)
    (h : E.ShallowValid) :
    E.Valid (D := D) := by
  unfold Valid ValidOn
  intro M _ hAxioms
  letI : Inhabited (Elem M) :=
    ⟨⟨M.carrier_nonempty.choose,
      M.carrier_nonempty.choose_spec⟩⟩
  apply
    (Sentence.shallowSat_ofFinStruct_iff_sat
      E.conjecture M).mp
  apply h (Elem M) (Shallow.ofFinStruct M)
  intro φ hφ
  apply
    (Sentence.shallowSat_ofFinStruct_iff_sat
      φ M).mpr
  exact hAxioms φ hφ

/- A shallow proof of the closed implication is valid. -/
theorem valid_of_implicationShallowValid
    (E : SentenceEntailment Λ)
    (h : E.ImplicationShallowValid) :
    E.Valid (D := D) :=
  valid_of_shallowValid E
    (shallowValid_of_implicationShallowValid E h)

end SentenceEntailment

end FOL
