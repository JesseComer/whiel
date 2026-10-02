-- Author: Jesse Comer
import Whiel.Cmd.Semantics

/-
  Abstract semantic Hoare logic for Whiel commands.

  Assertions are predicates on full-schema instances. This
  file deliberately stays abstract: it proves Hoare rules
  against `Cmd.BigStep`, without syntactic substitution or
  computable weakest/strongest predicate transformers.

  Key declarations: `Assertion`, `Assertion.andList`,
  `Assertion.orList`,
  `HoareValid`, `Hoare.hoareValid_congr_cmd`,
  `Hoare.wp`, `Hoare.wp_andList_apply_iff`,
  `Hoare.wp_orList_apply_iff`, `Hoare.sp`,
  `Hoare.hoareValid_while_of_vcs`, `Hoare.assign`,
  `Hoare.seq`, and `Hoare.ite`.
-/

------------------------------------------------------------
-- Semantic Assertions
------------------------------------------------------------

namespace Whiel

/- A semantic assertion over schema `Γ`. -/
abbrev Assertion
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  Instance D Γ → Prop

end Whiel

------------------------------------------------------------
-- Assertion Operations
------------------------------------------------------------

namespace Whiel

namespace Assertion

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Entailment between semantic assertions. -/
def entails
    (pre post : Assertion D Γ) : Prop :=
  ∀ I : Instance D Γ, pre I → post I

/- Semantic assertion equivalence. -/
def equiv
    (A₁ A₂ : Assertion D Γ) : Prop :=
  entails A₁ A₂ ∧ entails A₂ A₁

/- Semantic truth. -/
def top : Assertion D Γ :=
  fun _ => True

/- Semantic falsity. -/
def bottom : Assertion D Γ :=
  fun _ => False

/- Semantic conjunction. -/
def and
    (A₁ A₂ : Assertion D Γ) : Assertion D Γ :=
  fun I => A₁ I ∧ A₂ I

/- Semantic conjunction of a finite list of assertions. -/
def andList
    (As : List (Assertion D Γ)) : Assertion D Γ :=
  fun I => ∀ A₁ ∈ As, A₁ I

/- A finite semantic conjunction holds member-wise. -/
@[simp] theorem andList_apply_iff
    (As : List (Assertion D Γ))
    (I : Instance D Γ) :
    andList As I ↔ ∀ A₁ ∈ As, A₁ I :=
  Iff.rfl

/- A finite conjunction entails each of its members. -/
theorem andList_entails_of_mem
    {As : List (Assertion D Γ)}
    {A₁ : Assertion D Γ}
    (hMem : A₁ ∈ As) :
    entails (andList As) A₁ := by
  intro I hAs
  exact (andList_apply_iff As I).mp hAs A₁ hMem

/- Entailment into a finite conjunction is member-wise. -/
theorem entails_andList_iff
    (pre : Assertion D Γ)
    (posts : List (Assertion D Γ)) :
    entails pre (andList posts) ↔
      ∀ post ∈ posts, entails pre post := by
  constructor
  · intro hEntails post hMem I hPre
    exact
      (andList_apply_iff posts I).mp
        (hEntails I hPre) post hMem
  · intro hEntails I hPre
    apply (andList_apply_iff posts I).mpr
    intro post hMem
    exact hEntails post hMem I hPre

/- Semantic disjunction. -/
def or
    (A₁ A₂ : Assertion D Γ) : Assertion D Γ :=
  fun I => A₁ I ∨ A₂ I

/- Semantic disjunction of a finite list of assertions. -/
def orList
    (As : List (Assertion D Γ)) : Assertion D Γ :=
  fun I => ∃ A₁ ∈ As, A₁ I

/- A finite semantic disjunction holds member-wise. -/
@[simp] theorem orList_apply_iff
    (As : List (Assertion D Γ))
    (I : Instance D Γ) :
    orList As I ↔ ∃ A₁ ∈ As, A₁ I :=
  Iff.rfl

/- Semantic negation. -/
def not
    (A₁ : Assertion D Γ) : Assertion D Γ :=
  fun I => ¬ A₁ I

/- Semantic implication. -/
def imp
    (A₁ A₂ : Assertion D Γ) : Assertion D Γ :=
  fun I => A₁ I → A₂ I

/- Conjoin an assertion with a guard. -/
def andGuard
    (pre : Assertion D Γ)
    (G : Guard D Γ) : Assertion D Γ :=
  fun I => pre I ∧ G.eval I

/- Conjoin an assertion with the negation of a guard. -/
def andNotGuard
    (pre : Assertion D Γ)
    (G : Guard D Γ) : Assertion D Γ :=
  fun I => pre I ∧ ¬ G.eval I

/- Semantic assignment precondition. -/
def assignPre
    (post : Assertion D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    Assertion D Γ :=
  fun I => post (Instance.update I X (e.eval I))

end Assertion

end Whiel

------------------------------------------------------------
-- Hoare Assertion Views
------------------------------------------------------------

namespace Whiel

/-
  Types with a semantic interpretation as assertions over
  schema `Γ`.
-/
class ToAssertion
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A)
    (α : Type) where
  toAssertion : α → Assertion D Γ

variable {A D α : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Interpret a value as a semantic assertion. -/
def toAssertion
    [ToAssertion D Γ α]
    (x : α) : Assertion D Γ :=
  ToAssertion.toAssertion x

namespace Assertion

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Semantic assertions interpret as themselves. -/
instance instToAssertion :
    ToAssertion D Γ (Assertion D Γ) where
  toAssertion A₁ := A₁

end Assertion

end Whiel

------------------------------------------------------------
-- Hoare Validity
------------------------------------------------------------

namespace Whiel

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Hoare validity.

  `HoareValid pre C post` means every terminating run of `C`
  from a state satisfying `pre` ends in a state satisfying
  `post`, after interpreting `pre` and `post` as semantic
  assertions.
-/
def HoareValid
    {α β : Type}
    [ToAssertion D Γ α]
    [ToAssertion D Γ β]
    (pre : α)
    (C : Cmd D Γ)
    (post : β) : Prop :=
  ∀ I J : Instance D Γ,
    toAssertion pre I →
      Cmd.BigStep C I J →
        toAssertion post J

end Whiel

------------------------------------------------------------
-- Loop Big-Step Support
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  If a loop terminates, any property which is (1) true at
  the start of the loop and (2) preserved by the body when
  the guard is true is also true when the loop halts.
-/
theorem BigStep.while_invariant
    (Inv : Assertion D Γ)
    {Loop : Cmd D Γ}
    {I J : Instance D Γ}
    (hStep : BigStep Loop I J)
    {G : Guard D Γ}
    {C : Cmd D Γ}
    (hLoop : Loop = .while G C)
    (hBody :
      ∀ {K K' : Instance D Γ},
        BigStep C K K' → Inv K → G.eval K → Inv K')
    (hI : Inv I) :
    Inv J := by
  induction hStep with
  | skip I =>
      cases hLoop
  | assign I X e =>
      cases hLoop
  | seq hStep₁ hStep₂ ih₁ ih₂ =>
      cases hLoop
  | ite_true hG hStep ih =>
      cases hLoop
  | ite_false hG hStep ih =>
      cases hLoop
  | while_false hG =>
      cases hLoop
      exact hI
  | while_true hG hStepC hStepLoop ihC ihLoop =>
      cases hLoop
      have hNext : Inv _ :=
        hBody hStepC hI hG
      exact ihLoop rfl hNext

/-
  A terminating loop exits in a state falsifying its
  guard.
-/
theorem BigStep.while_final_not_guard
    {Loop : Cmd D Γ}
    {I J : Instance D Γ}
    (hStep : BigStep Loop I J)
    {G : Guard D Γ}
    {C : Cmd D Γ}
    (hLoop : Loop = .while G C) :
    ¬ G.eval J := by
  induction hStep with
  | skip I =>
      cases hLoop
  | assign I X e =>
      cases hLoop
  | seq hStep₁ hStep₂ ih₁ ih₂ =>
      cases hLoop
  | ite_true hG hStep ih =>
      cases hLoop
  | ite_false hG hStep ih =>
      cases hLoop
  | while_false hG =>
      cases hLoop
      exact hG
  | while_true hG hStepC hStepLoop ihC ihLoop =>
      cases hLoop
      exact ihLoop rfl

end Cmd

end Whiel

------------------------------------------------------------
-- Structural Hoare Rules
------------------------------------------------------------

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Command equivalence preserves Hoare validity. -/
theorem hoareValid_congr_cmd
    {α β : Type}
    [ToAssertion D Γ α]
    [ToAssertion D Γ β]
    {pre : α}
    {post : β}
    {C₁ C₂ : Cmd D Γ}
    (hC : Cmd.BigStepEquiv C₁ C₂) :
    HoareValid pre C₁ post ↔
      HoareValid pre C₂ post := by
  constructor
  · intro h I J hPre hStep
    exact h I J hPre ((hC I J).mpr hStep)
  · intro h I J hPre hStep
    exact h I J hPre ((hC I J).mp hStep)

/- Rule of consequence. -/
theorem consequence
    {pre pre' post post' : Assertion D Γ}
    {C : Cmd D Γ}
    (hPre : Assertion.entails pre' pre)
    (h : HoareValid pre C post)
    (hPost : Assertion.entails post post') :
    HoareValid pre' C post' := by
  intro I J hPre' hStep
  exact hPost J (h I J (hPre I hPre') hStep)

/- Strengthen the precondition of a valid triple. -/
theorem consequence_pre
    {pre pre' post : Assertion D Γ}
    {C : Cmd D Γ}
    (hPre : Assertion.entails pre' pre)
    (h : HoareValid pre C post) :
    HoareValid pre' C post :=
  consequence hPre h (fun _ hPost => hPost)

/- Weaken the postcondition of a valid triple. -/
theorem consequence_post
    {pre post post' : Assertion D Γ}
    {C : Cmd D Γ}
    (h : HoareValid pre C post)
    (hPost : Assertion.entails post post') :
    HoareValid pre C post' :=
  consequence (fun _ hPre => hPre) h hPost

/- Skip preserves any assertion. -/
theorem skip
    (A₁ : Assertion D Γ) :
    HoareValid A₁ (.skip : Cmd D Γ) A₁ := by
  intro I J hA₁ hStep
  have hJ : J = I :=
    (Cmd.bigStep_skip_iff I J).mp hStep
  rw [hJ]
  exact hA₁

/- Semantic assignment rule. -/
theorem assign
    (post : Assertion D Γ)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    HoareValid (Assertion.assignPre post X e) (.assign X e) post := by
  intro I J hPre hStep
  have hJ :
      J = Instance.update I X (e.eval I) :=
    (Cmd.bigStep_assign_iff I J X e).mp hStep
  rw [hJ]
  exact hPre

/- Sequencing rule. -/
theorem seq
    {pre A₁ post : Assertion D Γ}
    {C₁ C₂ : Cmd D Γ}
    (h₁ : HoareValid pre C₁ A₁)
    (h₂ : HoareValid A₁ C₂ post) :
    HoareValid pre (.seq C₁ C₂) post := by
  intro I J hPre hStep
  rcases (Cmd.bigStep_seq_iff C₁ C₂ I J).mp hStep
    with ⟨K, hStep₁, hStep₂⟩
  exact h₂ K J (h₁ I K hPre hStep₁) hStep₂

/- Conditional rule. -/
theorem ite
    {pre post : Assertion D Γ}
    (G : Guard D Γ)
    {C₁ C₂ : Cmd D Γ}
    (h₁ : HoareValid (Assertion.andGuard pre G) C₁ post)
    (h₂ : HoareValid (Assertion.andNotGuard pre G) C₂ post) :
    HoareValid pre (.ite G C₁ C₂) post := by
  intro I J hPre hStep
  rcases (Cmd.bigStep_ite_iff G C₁ C₂ I J).mp hStep
    with hThen | hElse
  · exact h₁ I J ⟨hPre, hThen.1⟩ hThen.2
  · exact h₂ I J ⟨hPre, hElse.1⟩ hElse.2

/- While rule with invariant `inv`. -/
theorem «while»
    (inv : Assertion D Γ)
    (G : Guard D Γ)
    (C : Cmd D Γ)
    (hBody : HoareValid (Assertion.andGuard inv G) C inv) :
    HoareValid inv (.while G C)
      (Assertion.andNotGuard inv G) := by
  intro I J hInv hStep
  have hInvFinal : inv J :=
    Cmd.BigStep.while_invariant inv hStep rfl
      (fun {K L} hStepC hInvK hGK =>
        hBody K L ⟨hInvK, hGK⟩ hStepC)
      hInv
  have hNotG : ¬ G.eval J :=
    Cmd.BigStep.while_final_not_guard hStep rfl
  exact ⟨hInvFinal, hNotG⟩

end Hoare

end Whiel

------------------------------------------------------------
-- Weakest Preconditions and Strongest Postconditions
------------------------------------------------------------

namespace Whiel

namespace Assertion

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  `pre.wpOf C post` says that `pre` is a weakest
  precondition for command `C` and postcondition `post`.
-/
def wpOf
    (pre : Assertion D Γ)
    (C : Cmd D Γ)
    (post : Assertion D Γ) : Prop :=
  HoareValid pre C post ∧
    ∀ pre' : Assertion D Γ,
      HoareValid pre' C post →
        entails pre' pre

/-
  `post.spOf pre C` says that `post` is a strongest
  postcondition for precondition `pre` and command `C`.
-/
def spOf
    (post : Assertion D Γ)
    (pre : Assertion D Γ)
    (C : Cmd D Γ) : Prop :=
  HoareValid pre C post ∧
    ∀ post' : Assertion D Γ,
      HoareValid pre C post' →
        entails post post'

/- Weakest preconditions are unique up to equivalence. -/
theorem wpOf_unique
    {pre₁ pre₂ post : Assertion D Γ}
    {C : Cmd D Γ}
    (h₁ : pre₁.wpOf C post)
    (h₂ : pre₂.wpOf C post) :
    equiv pre₁ pre₂ :=
  ⟨h₂.2 pre₁ h₁.1, h₁.2 pre₂ h₂.1⟩

/- Strongest postconditions are unique up to equivalence. -/
theorem spOf_unique
    {pre post₁ post₂ : Assertion D Γ}
    {C : Cmd D Γ}
    (h₁ : post₁.spOf pre C)
    (h₂ : post₂.spOf pre C) :
    equiv post₁ post₂ :=
  ⟨h₁.2 post₂ h₂.1, h₂.2 post₁ h₁.1⟩

end Assertion

namespace Hoare

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Abstract weakest precondition transformer. -/
def wp
    (C : Cmd D Γ)
    (post : Assertion D Γ) : Assertion D Γ :=
  fun I => ∀ J : Instance D Γ, Cmd.BigStep C I J → post J

/- Abstract strongest postcondition transformer. -/
def sp
    (C : Cmd D Γ)
    (pre : Assertion D Γ) : Assertion D Γ :=
  fun J => ∃ I : Instance D Γ, pre I ∧ Cmd.BigStep C I J

/- Hoare validity as entailment into `wp`. -/
theorem hoareValid_iff_entails_wp
    (pre post : Assertion D Γ)
    (C : Cmd D Γ) :
    HoareValid pre C post ↔
      Assertion.entails pre (wp C post) := by
  constructor
  · intro h I hPre J hStep
    exact h I J hPre hStep
  · intro h I J hPre hStep
    exact h I hPre J hStep

/- Hoare validity as entailment from `sp`. -/
theorem hoareValid_iff_sp_entails
    (pre post : Assertion D Γ)
    (C : Cmd D Γ) :
    HoareValid pre C post ↔
      Assertion.entails (sp C pre) post := by
  constructor
  · intro h J hSp
    rcases hSp with ⟨I, hPre, hStep⟩
    exact h I J hPre hStep
  · intro h I J hPre hStep
    exact h J ⟨I, hPre, hStep⟩

/- `wp` is a valid precondition for `C` and `post`. -/
theorem wp_valid
    (C : Cmd D Γ)
    (post : Assertion D Γ) :
    HoareValid (wp C post) C post :=
  (hoareValid_iff_entails_wp (wp C post) post C).mpr
    (fun _ h => h)

/- `wp` is the weakest valid precondition. -/
theorem wp_weakest
    {pre post : Assertion D Γ}
    {C : Cmd D Γ}
    (h : HoareValid pre C post) :
    Assertion.entails pre (wp C post) :=
  (hoareValid_iff_entails_wp pre post C).mp h

/-
  The canonical `wp` satisfies the weakest-precondition
  spec.
-/
theorem wp_wpOf
    (C : Cmd D Γ)
    (post : Assertion D Γ) :
    (wp C post).wpOf C post :=
  ⟨wp_valid C post, fun _ h => wp_weakest h⟩

/- `sp` is a valid postcondition for `C` and `pre`. -/
theorem sp_valid
    (C : Cmd D Γ)
    (pre : Assertion D Γ) :
    HoareValid pre C (sp C pre) :=
  (hoareValid_iff_sp_entails pre (sp C pre) C).mpr
    (fun _ h => h)

/- `sp` is the strongest valid postcondition. -/
theorem sp_strongest
    {pre post : Assertion D Γ}
    {C : Cmd D Γ}
    (h : HoareValid pre C post) :
    Assertion.entails (sp C pre) post :=
  (hoareValid_iff_sp_entails pre post C).mp h

/-
  The canonical `sp` satisfies the strongest-postcondition
  spec.
-/
theorem sp_spOf
    (C : Cmd D Γ)
    (pre : Assertion D Γ) :
    (sp C pre).spOf pre C :=
  ⟨sp_valid C pre, fun _ h => sp_strongest h⟩

/- `wp` is monotone in the postcondition. -/
theorem wp_mono
    {post post' : Assertion D Γ}
    (C : Cmd D Γ)
    (hPost : Assertion.entails post post') :
    Assertion.entails (wp C post) (wp C post') := by
  intro I hWp J hStep
  exact hPost J (hWp J hStep)

/- `wp` commutes pointwise with finite-conjunction formation. -/
theorem wp_andList_apply_iff
    (C : Cmd D Γ)
    (posts : List (Assertion D Γ))
    (I : Instance D Γ) :
    wp C (Assertion.andList posts) I ↔
      ∀ post ∈ posts, wp C post I := by
  constructor
  · intro hWp post hMem J hStep
    exact
      (Assertion.andList_apply_iff posts J).mp
        (hWp J hStep) post hMem
  · intro hWp J hStep
    apply (Assertion.andList_apply_iff posts J).mpr
    intro post hMem
    exact hWp post hMem J hStep

/-
  At a terminating state, `wp` commutes pointwise with
  finite-disjunction formation.
-/
theorem wp_orList_apply_iff
    (C : Cmd D Γ)
    (posts : List (Assertion D Γ))
    (I : Instance D Γ)
    (hTerm :
      ∃ J : Instance D Γ, Cmd.BigStep C I J) :
    wp C (Assertion.orList posts) I ↔
      ∃ post ∈ posts, wp C post I := by
  rcases hTerm with ⟨J, hStep⟩
  constructor
  · intro hWp
    rcases
        (Assertion.orList_apply_iff posts J).mp
          (hWp J hStep) with
      ⟨post, hMem, hPost⟩
    refine ⟨post, hMem, ?_⟩
    intro K hOther
    rw [Cmd.BigStep.deterministic hOther hStep]
    exact hPost
  · rintro ⟨post, hMem, hWp⟩ J hStep
    exact
      (Assertion.orList_apply_iff posts J).mpr
        ⟨post, hMem, hWp J hStep⟩

/- `sp` is monotone in the precondition. -/
theorem sp_mono
    {pre pre' : Assertion D Γ}
    (C : Cmd D Γ)
    (hPre : Assertion.entails pre pre') :
    Assertion.entails (sp C pre) (sp C pre') := by
  intro J hSp
  rcases hSp with ⟨I, hPreI, hStep⟩
  exact ⟨I, hPre I hPreI, hStep⟩

/- Adjunction between `sp` and `wp`. -/
theorem sp_wp_adjunction
    (pre post : Assertion D Γ)
    (C : Cmd D Γ) :
    Assertion.entails (sp C pre) post ↔
      Assertion.entails pre (wp C post) := by
  constructor
  · intro h
    exact (hoareValid_iff_entails_wp pre post C).mp
      ((hoareValid_iff_sp_entails pre post C).mpr h)
  · intro h
    exact (hoareValid_iff_sp_entails pre post C).mp
      ((hoareValid_iff_entails_wp pre post C).mpr h)

/-
  Init, maintenance, and termination entailments prove a
  while-loop Hoare triple.
-/
theorem hoareValid_while_of_vcs
    {pre inv post : Assertion D Γ}
    {G : Guard D Γ}
    {Body : Cmd D Γ}
    (hInit : Assertion.entails pre inv)
    (hMaint :
      Assertion.entails
        (Assertion.andGuard inv G)
        (wp Body inv))
    (hTerm :
      Assertion.entails
        (Assertion.andNotGuard inv G)
        post) :
    HoareValid pre (.while G Body) post := by
  have hBody :
      HoareValid
        (Assertion.andGuard inv G)
        Body
        inv :=
    (hoareValid_iff_entails_wp
      (Assertion.andGuard inv G) inv Body).mpr hMaint
  have hLoop :
      HoareValid inv (.while G Body)
        (Assertion.andNotGuard inv G) :=
    Hoare.while inv G Body hBody
  exact Hoare.consequence hInit hLoop hTerm

@[simp] theorem wp_skip_iff
    (post : Assertion D Γ)
    (I : Instance D Γ) :
    wp (.skip : Cmd D Γ) post I ↔ post I := by
  constructor
  · intro h
    exact h I (Cmd.BigStep.skip I)
  · intro h J hStep
    have hJ : J = I :=
      (Cmd.bigStep_skip_iff I J).mp hStep
    rw [hJ]
    exact h

@[simp] theorem sp_skip_iff
    (pre : Assertion D Γ)
    (J : Instance D Γ) :
    sp (.skip : Cmd D Γ) pre J ↔ pre J := by
  constructor
  · intro h
    rcases h with ⟨I, hPre, hStep⟩
    have hJ : J = I :=
      (Cmd.bigStep_skip_iff I J).mp hStep
    rw [hJ]
    exact hPre
  · intro h
    exact ⟨J, h, Cmd.BigStep.skip J⟩

@[simp] theorem wp_seq_iff
    (C₁ C₂ : Cmd D Γ)
    (post : Assertion D Γ)
    (I : Instance D Γ) :
    wp (.seq C₁ C₂) post I ↔ wp C₁ (wp C₂ post) I := by
  constructor
  · intro h K hStep₁ J hStep₂
    exact h J (Cmd.BigStep.seq hStep₁ hStep₂)
  · intro h J hStep
    rcases (Cmd.bigStep_seq_iff C₁ C₂ I J).mp hStep
      with ⟨K, hStep₁, hStep₂⟩
    exact h K hStep₁ J hStep₂

@[simp] theorem sp_seq_iff
    (C₁ C₂ : Cmd D Γ)
    (pre : Assertion D Γ)
    (J : Instance D Γ) :
    sp (.seq C₁ C₂) pre J ↔ sp C₂ (sp C₁ pre) J := by
  constructor
  · intro h
    rcases h with ⟨I, hPre, hStep⟩
    rcases (Cmd.bigStep_seq_iff C₁ C₂ I J).mp hStep
      with ⟨K, hStep₁, hStep₂⟩
    exact ⟨K, ⟨I, hPre, hStep₁⟩, hStep₂⟩
  · intro h
    rcases h with ⟨K, hSp, hStep₂⟩
    rcases hSp with ⟨I, hPre, hStep₁⟩
    exact ⟨I, hPre, Cmd.BigStep.seq hStep₁ hStep₂⟩

@[simp] theorem wp_ite_iff
    (G : Guard D Γ)
    (C₁ C₂ : Cmd D Γ)
    (post : Assertion D Γ)
    (I : Instance D Γ) :
    wp (.ite G C₁ C₂) post I ↔
      (G.eval I → wp C₁ post I) ∧
        (¬ G.eval I → wp C₂ post I) := by
  constructor
  · intro h
    constructor
    · intro hG J hStep
      exact h J (Cmd.BigStep.ite_true hG hStep)
    · intro hG J hStep
      exact h J (Cmd.BigStep.ite_false hG hStep)
  · intro h J hStep
    rcases (Cmd.bigStep_ite_iff G C₁ C₂ I J).mp hStep
      with hThen | hElse
    · exact h.1 hThen.1 J hThen.2
    · exact h.2 hElse.1 J hElse.2

@[simp] theorem sp_ite_iff
    (G : Guard D Γ)
    (C₁ C₂ : Cmd D Γ)
    (pre : Assertion D Γ)
    (J : Instance D Γ) :
    sp (.ite G C₁ C₂) pre J ↔
      sp C₁ (Assertion.andGuard pre G) J ∨
        sp C₂ (Assertion.andNotGuard pre G) J := by
  constructor
  · intro h
    rcases h with ⟨I, hPre, hStep⟩
    rcases (Cmd.bigStep_ite_iff G C₁ C₂ I J).mp hStep
      with hThen | hElse
    · exact Or.inl ⟨I, ⟨hPre, hThen.1⟩, hThen.2⟩
    · exact Or.inr ⟨I, ⟨hPre, hElse.1⟩, hElse.2⟩
  · intro h
    cases h with
    | inl hThen =>
        rcases hThen with ⟨I, hPre, hStep⟩
        exact ⟨I, hPre.1, Cmd.BigStep.ite_true hPre.2 hStep⟩
    | inr hElse =>
        rcases hElse with ⟨I, hPre, hStep⟩
        exact ⟨I, hPre.1, Cmd.BigStep.ite_false hPre.2 hStep⟩

@[simp] theorem wp_while_iff
    (G : Guard D Γ)
    (C : Cmd D Γ)
    (post : Assertion D Γ)
    (I : Instance D Γ) :
    wp (.while G C) post I ↔
      (¬ G.eval I → post I) ∧
        (G.eval I → wp C (wp (.while G C) post) I) := by
  constructor
  · intro h
    constructor
    · intro hG
      exact h I (Cmd.BigStep.while_false hG)
    · intro hG K hStepC J hStepLoop
      exact h J (Cmd.BigStep.while_true hG hStepC hStepLoop)
  · intro h J hStep
    rcases (Cmd.bigStep_while_iff G C I J).mp hStep
      with hFalse | hTrue
    · rw [hFalse.2]
      exact h.1 hFalse.1
    · rcases hTrue with ⟨K, hG, hStepC, hStepLoop⟩
      exact h.2 hG K hStepC J hStepLoop

end Hoare

end Whiel
