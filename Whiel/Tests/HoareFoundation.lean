-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Hoare.Preproc
import Whiel.Hoare.ProphecySchema

/-
  Focused checks for finite assertion connectives, exact
  loop-free weakest preconditions, and trusted framed-loop
  preprocessing provenance.
-/

------------------------------------------------------------
-- Finite Quantifier-Free Connectives
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace HoareFoundation

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

example (φ : QFAssertExpr D Γ) :
    QFAssertExpr.andList [φ] = φ := by
  rfl

example (φ ψ χ : QFAssertExpr D Γ) :
    QFAssertExpr.andList [φ, ψ, χ] =
      QFAssertExpr.and φ (QFAssertExpr.and ψ χ) := by
  rfl

example (φ : QFAssertExpr D Γ) :
    QFAssertExpr.orList [φ] = φ := by
  rfl

example (φ ψ χ : QFAssertExpr D Γ) :
    QFAssertExpr.orList [φ, ψ, χ] =
      QFAssertExpr.or φ (QFAssertExpr.or ψ χ) := by
  rfl

example (I : Instance D Γ) :
    (QFAssertExpr.andList
      ([] : List (QFAssertExpr D Γ))).eval I ↔ True := by
  simp

example (I : Instance D Γ) :
    (QFAssertExpr.orList
      ([] : List (QFAssertExpr D Γ))).eval I ↔
        False := by
  simp

example
    (φ : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (QFAssertExpr.andList [φ]).eval I ↔
      φ.eval I := by
  simp

example
    (φ : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (QFAssertExpr.orList [φ]).eval I ↔
      φ.eval I := by
  simp

example
    (φ ψ χ : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (QFAssertExpr.andList [φ, ψ, χ]).eval I ↔
      φ.eval I ∧ ψ.eval I ∧ χ.eval I := by
  simp

example
    (φ ψ χ : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (QFAssertExpr.orList [φ, ψ, χ]).eval I ↔
      φ.eval I ∨ ψ.eval I ∨ χ.eval I := by
  simp

example (φ : QFAssertExpr D Γ) : φ.entails φ :=
  QFAssertExpr.entails_refl φ

end HoareFoundation

end Tests

end Whiel

------------------------------------------------------------
-- Direct Quantifier-Free Weakest Preconditions
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace HoareFoundation

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

example
    (post : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (QFAssertExpr.wpLoopFree
      (.skip : Cmd D Γ) Cmd.loopFree_skip post).eval I ↔
        post.eval I := by
  rw [QFAssertExpr.wpLoopFree_eval_iff]
  exact Hoare.wp_skip_iff post.eval I

example
    (post : QFAssertExpr D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X))
    (I : Instance D Γ) :
    (QFAssertExpr.wpLoopFree
      (.assign X e) (Cmd.loopFree_assign X e) post).eval
        I ↔
      post.eval (Instance.update I X (e.eval I)) := by
  rw [QFAssertExpr.wpLoopFree_eval_iff]
  exact Hoare.wp_assign_iff post.eval X e I

example
    (C₁ C₂ : Cmd D Γ)
    (h₁ : C₁.LoopFree)
    (h₂ : C₂.LoopFree)
    (post : QFAssertExpr D Γ) :
    QFAssertExpr.wpLoopFree
        (.seq C₁ C₂) ⟨h₁, h₂⟩ post =
      QFAssertExpr.wpLoopFree C₁ h₁
        (QFAssertExpr.wpLoopFree C₂ h₂ post) := by
  rfl

example
    (C : Cmd D Γ)
    (hC : C.LoopFree)
    (posts : List (QFAssertExpr D Γ)) :
    (QFAssertExpr.wpLoopFree C hC
      (QFAssertExpr.andList posts)).equiv
        (QFAssertExpr.andList
          (posts.map (QFAssertExpr.wpLoopFree C hC))) :=
  QFAssertExpr.wpLoopFree_andList_equiv C hC posts

end HoareFoundation

end Tests

end Whiel

------------------------------------------------------------
-- Framed-Loop Source Provenance
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace HoareFoundation

open Whiel.Concrete
open Hoare.Preproc

def frameSchema : UnnamedSchema ProgramNames :=
  programSch![
    {R, S, S_2, Out} (arity: 1)
  ]

def framePre : AssertExpr Data frameSchema :=
  programAssert![
    true
  ]

def frameCmd : Cmd Data frameSchema :=
  programCmd![
    { ExecSchema: frameSchema }
    {
      S_2 := ∅;
      S := R;
      WHILE (S ≠ S_2) DO
        S_2 := S;
        S := R
      END;
      Out := S
    }
  ]

def framePost : AssertExpr Data frameSchema :=
  programAssert![
    Out = S
  ]

def framePreproc :
    Hoare.Preproc framePre frameCmd framePost :=
  Hoare.preprocess framePre frameCmd framePost

/-
  The source is already a framed loop with a preamble that
  the split keeps whole, so no flag is drawn and the
  preprocessed loop lives over the input schema itself.
-/
theorem frame_outSchema :
    framePreproc.outSchema.syms = frameSchema.syms := by
  decide +kernel

theorem frame_normalized_init :
    loopOnlyInitValid
      framePreproc.loopPre framePreproc.loopPre := by
  intro I hI
  exact hI

/-
  Checking initialization at the loop head loses no
  invariant: the source-prefix obligation implies it.
-/
example
    (hSource :
      framePreproc.sourcePrefixInitValid
        (by decide) framePreproc.loopPre) :
    loopOnlyInitValid
      framePreproc.loopPre framePreproc.loopPre :=
  loopOnlyInitValid_of_sourcePrefixInitValid _ _ _ hSource

/- Provenance: the loop head is fixed by the prefix. -/
example :
    forall u : Instance Data framePreproc.outSchema,
      framePreproc.loopPre.eval u ->
        framePre.eval
            (Preprocess.project framePreproc.outExtends u) ∧
          Cmd.BigStep framePreproc.sourcePrefix u u :=
  framePreproc.loopPre_source_fixed

/- Provenance: every lifted start reaches the loop head. -/
example :
    forall (s : Instance Data frameSchema)
      (u : Instance Data framePreproc.outSchema),
      framePre.eval s ->
        Cmd.BigStep framePreproc.sourcePrefix
            (Preprocess.lift framePreproc.outExtends s) u ->
          framePreproc.loopPre.eval u :=
  framePreproc.loopPre_source_reaches

/- The framed command is the whole preprocessed loop. -/
example :
    framePreproc.framedCmd =
      .seq framePreproc.sourcePrefix
        (.seq framePreproc.loopCmd framePreproc.sourceClose) :=
  rfl

/- The closing assertion is the suffix's exact WP. -/
example :
    framePreproc.loopPost =
      AssertExpr.wpLoopFree framePreproc.sourceClose
        framePreproc.sourceClose_loopFree
        (Preprocess.retagAssert framePreproc.outExtends
          framePost (by decide)) :=
  rfl

end HoareFoundation

end Tests

end Whiel
