-- Author: Jesse Comer
import Whiel.Cmd.Semantics

/-
  Framed loops for the generic Whiel preprocessor.

  A framed loop is the quadruple the preprocessor carries
  through its recursion: a loop-free prefix, a guard, a
  loop-free body, and a loop-free suffix. Its unfolding is
  the command `P; while G do B end; S`.

  Key definitions include:
    * `Whiel.Preprocess.loops`
    * `Whiel.Preprocess.LoopFree`
    * `Whiel.Preprocess.Framed`
    * `Whiel.Preprocess.Framed.unfold`
    * `Whiel.Preprocess.Framed.base`

  Loop-freeness is a predicate on the components
  (`Framed.LoopFreeParts`) and not a field of the
  structure. The transformation must reduce by evaluation
  on concrete inputs, so the operations are plain data
  functions with no proof arguments to build; preservation
  of loop-freeness is a separate lemma per operation.

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Loop Counting
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The number of `while` nodes of a command. -/
def loops : Cmd D Γ → Nat
| .skip => 0
| .assign _ _ => 0
| .seq C₁ C₂ => loops C₁ + loops C₂
| .ite _ C₁ C₂ => loops C₁ + loops C₂
| .«while» _ C => loops C + 1

/- A command is loop-free when it has no `while` node. -/
def LoopFree (C : Cmd D Γ) : Prop :=
  loops C = 0

instance (C : Cmd D Γ) : Decidable (LoopFree C) := by
  unfold LoopFree
  infer_instance

@[simp] theorem loopFree_skip :
    LoopFree (.skip : Cmd D Γ) :=
  rfl

@[simp] theorem loopFree_assign
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    LoopFree (.assign X e) :=
  rfl

@[simp] theorem loopFree_seq_iff
    (C₁ C₂ : Cmd D Γ) :
    LoopFree (.seq C₁ C₂) ↔
      LoopFree C₁ ∧ LoopFree C₂ := by
  simp [LoopFree, loops]

@[simp] theorem loopFree_ite_iff
    (G : Guard D Γ)
    (C₁ C₂ : Cmd D Γ) :
    LoopFree (.ite G C₁ C₂) ↔
      LoopFree C₁ ∧ LoopFree C₂ := by
  simp [LoopFree, loops]

@[simp] theorem not_loopFree_while
    (G : Guard D Γ)
    (C : Cmd D Γ) :
    ¬ LoopFree (.while G C) := by
  simp [LoopFree, loops]

end Preprocess

end Whiel

------------------------------------------------------------
-- Framed Loops
------------------------------------------------------------

namespace Whiel

namespace Preprocess

/-
  A framed loop over `Γ`. The note's prefix and suffix are
  `init` and `close`, matching the repository's existing
  vocabulary for the loop-free code around a loop.
-/
structure Framed
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type where
  init : Cmd D Γ
  guard : Guard D Γ
  body : Cmd D Γ
  close : Cmd D Γ

namespace Framed

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The unfolding `P; while G do B end; S`. -/
def unfold (L : Framed D Γ) : Cmd D Γ :=
  .seq L.init (.seq (.while L.guard L.body) L.close)

/- The base framed loop of a loop-free command. -/
def base (C : Cmd D Γ) : Framed D Γ where
  init := .skip
  guard := .«false»
  body := .skip
  close := C

@[simp] theorem base_init
    (C : Cmd D Γ) :
    (base C).init = .skip :=
  rfl

@[simp] theorem base_guard
    (C : Cmd D Γ) :
    (base C).guard = .«false» :=
  rfl

@[simp] theorem base_body
    (C : Cmd D Γ) :
    (base C).body = .skip :=
  rfl

@[simp] theorem base_close
    (C : Cmd D Γ) :
    (base C).close = C :=
  rfl

/- The loop-free components are loop-free. -/
def LoopFreeParts (L : Framed D Γ) : Prop :=
  LoopFree L.init ∧ LoopFree L.body ∧ LoopFree L.close

instance (L : Framed D Γ) :
    Decidable L.LoopFreeParts := by
  unfold LoopFreeParts
  infer_instance

/- Recognizer for framed loops of base shape. -/
def IsBase (L : Framed D Γ) : Prop :=
  L.init = .skip ∧ L.guard = .«false» ∧
    L.body = .skip

@[simp] theorem isBase_base
    (C : Cmd D Γ) :
    IsBase (base C) :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem loopFreeParts_base_iff
    (C : Cmd D Γ) :
    LoopFreeParts (base C) ↔ LoopFree C := by
  simp [LoopFreeParts, base]

/- A framed loop of base shape is its own suffix. -/
theorem eq_base_of_isBase
    {L : Framed D Γ}
    (hBase : L.IsBase) :
    L = base L.close := by
  cases L with
  | mk init guard body close =>
      cases hBase with
      | intro hInit hRest =>
          cases hRest with
          | intro hGuard hBody =>
              simp_all [base]

/- The unfolding of a framed loop has exactly one loop. -/
theorem loops_unfold
    {L : Framed D Γ}
    (hParts : L.LoopFreeParts) :
    loops L.unfold = 1 := by
  rcases hParts with ⟨hInit, hBody, hClose⟩
  simp [unfold, loops, LoopFree] at *
  omega

end Framed

end Preprocess

end Whiel

------------------------------------------------------------
-- Framed Loop Semantics
------------------------------------------------------------

namespace Whiel

namespace Preprocess

namespace Framed

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

theorem bigStep_unfold_iff
    (L : Framed D Γ)
    (I J : Instance D Γ) :
    Cmd.BigStep L.unfold I J ↔
      ∃ K₁ K₂ : Instance D Γ,
        Cmd.BigStep L.init I K₁ ∧
          Cmd.BigStep (.while L.guard L.body) K₁ K₂ ∧
            Cmd.BigStep L.close K₂ J := by
  simp only [unfold, Cmd.bigStep_seq_iff]
  constructor
  · rintro ⟨K₁, h₁, K₂, h₂, h₃⟩
    exact ⟨K₁, K₂, h₁, h₂, h₃⟩
  · rintro ⟨K₁, K₂, h₁, h₂, h₃⟩
    exact ⟨K₁, h₁, K₂, h₂, h₃⟩

/- A never-entered loop runs from a state to itself. -/
theorem bigStep_while_false_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    Cmd.BigStep (.while (.«false» : Guard D Γ) C) I J ↔
      J = I := by
  constructor
  · intro h
    cases h with
    | while_false hG => rfl
    | while_true hG hBody hLoop =>
        exact absurd hG (by simp [Guard.eval])
  · intro h
    subst h
    exact Cmd.BigStep.while_false (by simp [Guard.eval])

/- The base framed loop runs exactly like its suffix. -/
theorem bigStep_base_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    Cmd.BigStep (base C).unfold I J ↔
      Cmd.BigStep C I J := by
  rw [bigStep_unfold_iff]
  constructor
  · rintro ⟨K₁, K₂, hInit, hLoop, hClose⟩
    have hK₁ : K₁ = I :=
      (Cmd.bigStep_skip_iff I K₁).mp hInit
    subst hK₁
    have hK₂ : K₂ = K₁ :=
      (bigStep_while_false_iff _ K₁ K₂).mp hLoop
    subst hK₂
    exact hClose
  · intro h
    exact
      ⟨I, I, Cmd.BigStep.skip I,
        (bigStep_while_false_iff _ I I).mpr rfl, h⟩

end Framed

end Preprocess

end Whiel
