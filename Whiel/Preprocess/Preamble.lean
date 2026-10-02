-- Author: Jesse Comer
import Whiel.Preprocess.Normalize
import Whiel.Hoare.Concrete

/-
  The preamble split and the preamble push.

  The loop-head assertion of the single-loop triple is the
  strongest postcondition of the input precondition through
  the framed loop's prefix, and that computation stays
  quantifier-free only under a syntactic condition on the
  prefix's assignments. Rather than demand the condition,
  the preprocessor keeps outside the loop exactly the
  largest initial part of the prefix that satisfies it and
  pushes the rest into the loop body under one more flag.
  The push is the total fallback, and with it every command
  has an output.

  The prefix is first flattened into top-level items, each
  an assignment or a conditional, with `skip`s dropped; a
  conditional is atomic for the split, since its strongest
  postcondition is defined only when both branches are.

  Key definitions include:
    * `Whiel.Preprocess.seqItems`
    * `Whiel.Preprocess.splitItems`
    * `Whiel.Preprocess.pushFramed`
    * `Whiel.Preprocess.retagAssert`

  Correctness is proven by:
    * `Whiel.Preprocess.pushFramed_equivMod`
    * `Whiel.Preprocess.pushFramed_flag_down`
    * `Whiel.Preprocess.splitItems_keep_sp`
    * `Whiel.Preprocess.loopHead_fixed`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Loop-Freeness In Both Spellings
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The preprocessor counts `while` nodes and the Hoare
  library recurses on the constructor; the two spellings of
  loop-freeness agree.
-/
theorem cmdLoopFree_iff_loopFree
    (C : Cmd D Γ) :
    C.LoopFree ↔ LoopFree C := by
  induction C with
  | skip => simp [Cmd.LoopFree, LoopFree, loops]
  | assign X e => simp [Cmd.LoopFree, LoopFree, loops]
  | seq C₁ C₂ ih₁ ih₂ =>
      rw [Cmd.LoopFree, loopFree_seq_iff, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      rw [Cmd.LoopFree, loopFree_ite_iff, ih₁, ih₂]
  | «while» G C ih =>
      simp only [Cmd.LoopFree]
      exact
        ⟨False.elim, fun h => not_loopFree_while G C h⟩

/- The Hoare library's spelling of a loop-free command. -/
theorem cmdLoopFree_of_loopFree
    {C : Cmd D Γ}
    (hFree : LoopFree C) :
    C.LoopFree :=
  (cmdLoopFree_iff_loopFree C).mpr hFree

end Preprocess

end Whiel

------------------------------------------------------------
-- The Prefix As Top-Level Items
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Flatten a command into its top-level sequence items, with
  `skip`s dropped. A conditional is one item, and is atomic
  for the split of the note's Section 4.1.
-/
def seqItems : Cmd D Γ → List (Cmd D Γ)
| .skip => []
| .seq C₁ C₂ => seqItems C₁ ++ seqItems C₂
| .assign X e => [.assign X e]
| .ite G C₁ C₂ => [.ite G C₁ C₂]
| .«while» G C => [.«while» G C]

/- Rebuild a command from a list of items. -/
def seqOfItems : List (Cmd D Γ) → Cmd D Γ
| [] => .skip
| C :: rest => .seq C (seqOfItems rest)

/- A trailing `skip` changes no run. -/
theorem bigStep_seq_skip_right_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    Cmd.BigStep (.seq C .skip) I J ↔
      Cmd.BigStep C I J := by
  rw [Cmd.bigStep_seq_iff]
  constructor
  · rintro ⟨K, hC, hSkip⟩
    rw [(Cmd.bigStep_skip_iff K J).mp hSkip]
    exact hC
  · intro h
    exact ⟨J, h, Cmd.BigStep.skip J⟩

/- Rebuilding an appended list is a sequence. -/
theorem bigStepEquiv_seqOfItems_append
    (items rest : List (Cmd D Γ)) :
    Cmd.BigStepEquiv (seqOfItems (items ++ rest))
      (.seq (seqOfItems items) (seqOfItems rest)) := by
  induction items with
  | nil =>
      intro I J
      simp only [List.nil_append, seqOfItems,
        Cmd.bigStep_seq_iff]
      constructor
      · intro h
        exact ⟨I, Cmd.BigStep.skip I, h⟩
      · rintro ⟨K, hSkip, h⟩
        rw [(Cmd.bigStep_skip_iff I K).mp hSkip] at h
        exact h
  | cons C items ih =>
      intro I J
      have ih' :
          ∀ K L : Instance D Γ,
            Cmd.BigStep (seqOfItems (items ++ rest)) K L ↔
              ∃ M : Instance D Γ,
                Cmd.BigStep (seqOfItems items) K M ∧
                  Cmd.BigStep (seqOfItems rest) M L := by
        intro K L
        rw [ih K L, Cmd.bigStep_seq_iff]
      simp only [List.cons_append, seqOfItems,
        Cmd.bigStep_seq_iff, ih']
      constructor
      · rintro ⟨K, hC, L, hOne, hTwo⟩
        exact ⟨L, ⟨K, hC, hOne⟩, hTwo⟩
      · rintro ⟨L, ⟨K, hC, hOne⟩, hTwo⟩
        exact ⟨K, hC, L, hOne, hTwo⟩

/- The items of a command run exactly as the command. -/
theorem bigStepEquiv_seqOfItems_seqItems
    (C : Cmd D Γ) :
    Cmd.BigStepEquiv (seqOfItems (seqItems C)) C := by
  induction C with
  | skip => intro I J; rfl
  | assign X e =>
      intro I J
      exact bigStep_seq_skip_right_iff _ I J
  | seq C₁ C₂ ih₁ ih₂ =>
      intro I J
      refine
        Iff.trans
          (bigStepEquiv_seqOfItems_append
            (seqItems C₁) (seqItems C₂) I J) ?_
      simp only [Cmd.bigStep_seq_iff]
      constructor
      · rintro ⟨K, hOne, hTwo⟩
        exact ⟨K, (ih₁ I K).mp hOne, (ih₂ K J).mp hTwo⟩
      · rintro ⟨K, hOne, hTwo⟩
        exact ⟨K, (ih₁ I K).mpr hOne, (ih₂ K J).mpr hTwo⟩
  | ite G C₁ C₂ ih₁ ih₂ =>
      intro I J
      exact bigStep_seq_skip_right_iff _ I J
  | «while» G C ih =>
      intro I J
      exact bigStep_seq_skip_right_iff _ I J

/- Every item of a loop-free command is loop-free. -/
theorem loopFree_of_mem_seqItems
    {C : Cmd D Γ}
    (hFree : LoopFree C) :
    ∀ I ∈ seqItems C, LoopFree I := by
  induction C with
  | skip => intro I hI; cases hI
  | assign X e =>
      intro I hI
      simp only [seqItems, List.mem_singleton] at hI
      rw [hI]
      exact loopFree_assign X e
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases (loopFree_seq_iff C₁ C₂).mp hFree with
        ⟨h₁, h₂⟩
      intro I hI
      rcases List.mem_append.mp hI with h | h
      · exact ih₁ h₁ I h
      · exact ih₂ h₂ I h
  | ite G C₁ C₂ ih₁ ih₂ =>
      intro I hI
      simp only [seqItems, List.mem_singleton] at hI
      rw [hI]
      exact hFree
  | «while» G C ih =>
      exact absurd hFree (not_loopFree_while G C)

/- Rebuilding loop-free items gives loop-free code. -/
theorem loopFree_seqOfItems
    {items : List (Cmd D Γ)}
    (hAll : ∀ I ∈ items, LoopFree I) :
    LoopFree (seqOfItems items) := by
  induction items with
  | nil => exact loopFree_skip
  | cons C rest ih =>
      refine (loopFree_seq_iff C (seqOfItems rest)).mpr ?_
      refine ⟨hAll C (by simp), ih ?_⟩
      intro I hI
      exact hAll I (by simp [hI])

end Preprocess

end Whiel

------------------------------------------------------------
-- Retagging A Quantifier-Free Assertion
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  The assertion clause of Lemma "Retagging": a
  quantifier-free assertion over `Δ`, read over an extending
  schema. Its formula lives over the assertion's own full
  schema, which a quantifier-free assertion shares with `Δ`,
  so it moves to `Δ` and then to `Ω` by the guard's own
  reinterpretation.
-/
def retagAssert
    (hExt : Ω.extensionOf Δ)
    (φ : AssertExpr D Δ)
    (hNo : φ.NoBoundSymbols) :
    AssertExpr D Ω :=
  AssertExpr.ofQF
    ((φ.toQFOfNoBound hNo).onExtension hExt)

/- A retagged assertion is quantifier-free. -/
theorem retagAssert_noBoundSymbols
    (hExt : Ω.extensionOf Δ)
    (φ : AssertExpr D Δ)
    (hNo : φ.NoBoundSymbols) :
    (retagAssert hExt φ hNo).NoBoundSymbols :=
  AssertExpr.ofQF_noBound _

/-
  Lemma "Retagging" for assertions: the value of a
  quantifier-free assertion over `Δ`, read over `Ω`, at a
  state is its value at the projection.
-/
theorem retag_assert_eval_iff
    (hExt : Ω.extensionOf Δ)
    (φ : AssertExpr D Δ)
    (hNo : φ.NoBoundSymbols)
    (I : Instance D Ω) :
    (retagAssert hExt φ hNo).eval I ↔
      φ.eval (project hExt I) := by
  rw [retagAssert, AssertExpr.ofQF_eval_iff,
    retag_eval_iff hExt (φ.toQFOfNoBound hNo) I]
  exact AssertExpr.toQFOfNoBound_eval_iff φ hNo _

end Preprocess

end Whiel

------------------------------------------------------------
-- The Split Of The Preamble
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The split of the note's Section 4.1: the largest prefix of
  the prefix whose strongest postcondition stays
  quantifier-free, the assertion it reaches, and the rest.
-/
structure PreambleSplit
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type where
  keep : List (Cmd D Γ)
  mid : AssertExpr D Γ
  push : List (Cmd D Γ)

/-
  Walk the items, keeping each one whose quantifier-free
  strongest postcondition is defined and pushing everything
  from the first obstructing item onward: once an item is
  pushed the items after it must follow, since they run
  after it.
-/
def splitItems :
    List (Cmd D Γ) → AssertExpr D Γ → PreambleSplit D Γ
| [], φ => ⟨[], φ, []⟩
| I :: rest, φ =>
    if hFree : LoopFree I then
      match
        AssertExpr.spLoopFreeNoFresh? I
          (cmdLoopFree_of_loopFree hFree) φ with
      | some ψ =>
          let tail := splitItems rest ψ
          ⟨I :: tail.keep, tail.mid, tail.push⟩
      | none => ⟨[], φ, I :: rest⟩
    else ⟨[], φ, I :: rest⟩

/- The split partitions the items in order. -/
theorem splitItems_keep_append_push
    (items : List (Cmd D Γ))
    (φ : AssertExpr D Γ) :
    (splitItems items φ).keep ++
        (splitItems items φ).push =
      items := by
  induction items generalizing φ with
  | nil => rfl
  | cons I rest ih =>
      rw [splitItems]
      by_cases hFree : LoopFree I
      · rw [dif_pos hFree]
        cases hSP :
            AssertExpr.spLoopFreeNoFresh? I
              (cmdLoopFree_of_loopFree hFree) φ with
        | none => rfl
        | some ψ =>
            simpa using ih ψ
      · rw [dif_neg hFree]
        rfl

/- The kept items are items of the input. -/
theorem mem_of_mem_splitItems_keep
    {items : List (Cmd D Γ)}
    {φ : AssertExpr D Γ}
    {I : Cmd D Γ}
    (hMem : I ∈ (splitItems items φ).keep) :
    I ∈ items := by
  rw [← splitItems_keep_append_push items φ]
  exact List.mem_append.mpr (Or.inl hMem)

/- The pushed items are items of the input. -/
theorem mem_of_mem_splitItems_push
    {items : List (Cmd D Γ)}
    {φ : AssertExpr D Γ}
    {I : Cmd D Γ}
    (hMem : I ∈ (splitItems items φ).push) :
    I ∈ items := by
  rw [← splitItems_keep_append_push items φ]
  exact List.mem_append.mpr (Or.inr hMem)

/-
  The prefix is the kept part followed by the pushed part,
  so nothing is lost and nothing is reordered.
-/
theorem bigStepEquiv_splitItems
    (C : Cmd D Γ)
    (φ : AssertExpr D Γ) :
    Cmd.BigStepEquiv
      (.seq (seqOfItems (splitItems (seqItems C) φ).keep)
        (seqOfItems (splitItems (seqItems C) φ).push))
      C := by
  refine
    Cmd.BigStepEquiv.trans
      (Cmd.BigStepEquiv.symm
        (bigStepEquiv_seqOfItems_append _ _)) ?_
  rw [splitItems_keep_append_push]
  exact bigStepEquiv_seqOfItems_seqItems C

end Preprocess

end Whiel

------------------------------------------------------------
-- The Quantifier-Free Strongest Postcondition Of The Keep
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The sequence clause of Definition "Quantifier-free
  strongest postcondition", read at the assertion level: the
  two steps compose, each undefined branch propagating. Both
  results carry the input's own full schema and extension
  witness, so the second step is the first's continuation.
-/
theorem spLoopFreeNoFresh?_seq
    {C₁ C₂ : Cmd D Γ}
    (hFree : (Cmd.seq C₁ C₂).LoopFree)
    (pre : AssertExpr D Γ) :
    AssertExpr.spLoopFreeNoFresh? (.seq C₁ C₂) hFree pre =
      (AssertExpr.spLoopFreeNoFresh? C₁ hFree.1
          pre).bind
        (fun ψ =>
          AssertExpr.spLoopFreeNoFresh? C₂ hFree.2 ψ) := by
  simp only [AssertExpr.spLoopFreeNoFresh?,
    AssertExpr.spLoopFreeNoFreshFormula?]
  cases hOne :
      AssertExpr.spLoopFreeNoFreshFormula? pre.extendsFree
        C₁ hFree.1 pre.formula with
  | none => simp
  | some ψ => simp

/-
  The kept part's quantifier-free strongest postcondition is
  the assertion the split reached: this is Definition
  "Preamble push"'s `φ_m`, and when nothing is pushed it is
  `φ_k`.
-/
theorem splitItems_keep_sp
    (items : List (Cmd D Γ))
    (φ : AssertExpr D Γ)
    (hKeep :
      (seqOfItems (splitItems items φ).keep).LoopFree) :
    AssertExpr.spLoopFreeNoFresh?
        (seqOfItems (splitItems items φ).keep) hKeep φ =
      some (splitItems items φ).mid := by
  induction items generalizing φ with
  | nil =>
      simp only [AssertExpr.spLoopFreeNoFresh?]
      rfl
  | cons I rest ih =>
      revert hKeep
      rw [splitItems]
      by_cases hFree : LoopFree I
      · rw [dif_pos hFree]
        cases hSP :
            AssertExpr.spLoopFreeNoFresh? I
              (cmdLoopFree_of_loopFree hFree) φ with
        | none =>
            intro hKeep
            simp only [AssertExpr.spLoopFreeNoFresh?]
            rfl
        | some ψ =>
            intro hKeep
            have hTail :
                (seqOfItems
                  (splitItems rest ψ).keep).LoopFree :=
              hKeep.2
            change
              AssertExpr.spLoopFreeNoFresh?
                  (Cmd.seq I
                    (seqOfItems
                      (splitItems rest ψ).keep))
                  hKeep φ =
                some (splitItems rest ψ).mid
            rw [spLoopFreeNoFresh?_seq hKeep φ,
              show
                AssertExpr.spLoopFreeNoFresh? I hKeep.1
                    φ =
                  some ψ from hSP]
            simpa using ih ψ hTail
      · rw [dif_neg hFree]
        intro hKeep
        simp only [AssertExpr.spLoopFreeNoFresh?]
        rfl

end Preprocess

end Whiel

------------------------------------------------------------
-- The Preamble Push
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The pushed guard: the push flag or the source guard. -/
def pushGuard
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (G : Guard D Δ) :
    Guard D Ω :=
  .or p.test (G.onExtension hExt)

/-
  The pushed body. With `p` up it is the pushed part of the
  preamble, run once and followed by lowering `p`; with `p`
  down it is the original body.
-/
def pushBody
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (Push B : Cmd D Δ) :
    Cmd D Ω :=
  .ite p.test
    (.seq (retag hExt Push) p.lower)
    (retag hExt B)

/-
  Definition "Preamble push": the prefix keeps the kept part
  and raises `p`, the guard gains `p` as a disjunct, the
  body gains the pushed part under `p`, and the suffix is
  unchanged.
-/
def pushFramed
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (Keep Push : Cmd D Δ)
    (L : Framed D Δ) :
    Framed D Ω where
  init := .seq (retag hExt Keep) p.raise
  guard := pushGuard hExt p L.guard
  body := pushBody hExt p Push L.body
  close := retag hExt L.close

/- With the flag up the pushed guard is true. -/
theorem pushGuard_of_up
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (G : Guard D Δ)
    {I : Instance D Ω}
    (hUp : p.Up I) :
    (pushGuard hExt p G).eval I :=
  Or.inl hUp

/- With the flag down the source guard decides. -/
theorem pushGuard_eval_down
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (G : Guard D Δ)
    {I : Instance D Ω}
    (hDown : ¬ p.Up I) :
    ((pushGuard hExt p G).eval I ↔
      G.eval (project hExt I)) := by
  rw [pushGuard, Guard.eval, ← retag_eval_iff hExt G I]
  constructor
  · rintro (hUp | hG)
    · exact absurd hUp hDown
    · exact hG
  · intro hG
    exact Or.inr hG

end Preprocess

end Whiel

------------------------------------------------------------
-- The Push Lemma, Forward
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  A run of the pushed loop projects to a run of the source
  loop, preceded by the pushed part when the flag is up on
  entry; either way the flag is down at the end.
-/
theorem pushLoop_project
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (hFresh : p.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (Push B : Cmd D Δ)
    {u v : Instance D Ω}
    (hStep :
      Cmd.BigStep
        (.«while» (pushGuard hExt p G)
          (pushBody hExt p Push B)) u v) :
    (p.Up u →
        Cmd.BigStep (.seq Push (.«while» G B))
            (project hExt u) (project hExt v) ∧
          ¬ p.Up v) ∧
      (¬ p.Up u →
        Cmd.BigStep (.«while» G B)
            (project hExt u) (project hExt v) ∧
          ¬ p.Up v) := by
  generalize hW :
      (Cmd.«while» (pushGuard hExt p G)
        (pushBody hExt p Push B) : Cmd D Ω) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false Gu Bo u hFalse =>
      cases hW
      constructor
      · intro hUp
        exact
          absurd (pushGuard_of_up hExt p G hUp) hFalse
      · intro hDown
        refine ⟨Cmd.BigStep.while_false ?_, hDown⟩
        intro hG
        exact hFalse
          ((pushGuard_eval_down hExt p G hDown).mpr hG)
  | @while_true Gu Bo u m v hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      constructor
      · intro hUp
        rcases
          (Cmd.bigStep_ite_iff _ _ _ u m).mp hRun with
          hT | hF
        · rcases
            (Cmd.bigStep_seq_iff _ _ u m).mp hT.2 with
            ⟨m₁, hPush, hLower⟩
          have hDownM : ¬ p.Up m :=
            FlagSym.not_up_of_bigStep_lower hLower
          have hProjM :
              project hExt m = project hExt m₁ :=
            project_of_bigStep_lower hExt hFresh hLower
          rcases (ihLoop rfl).2 hDownM with
            ⟨hTail, hDownV⟩
          refine ⟨?_, hDownV⟩
          have hRunPush :
              Cmd.BigStep Push (project hExt u)
                (project hExt m) := by
            rw [hProjM]
            exact retag_bigStep_project hExt hPush
          exact
            Cmd.BigStep.seq (I₁ := project hExt m)
              hRunPush hTail
        · exact absurd hUp hF.1
      · intro hDown
        rcases
          (Cmd.bigStep_ite_iff _ _ _ u m).mp hRun with
          hT | hF
        · exact absurd hT.1 hDown
        · have hDownM : ¬ p.Up m :=
            hoist_down_pres hExt hFresh B u m hDown hF.2
          rcases (ihLoop rfl).2 hDownM with
            ⟨hTail, hDownV⟩
          refine ⟨?_, hDownV⟩
          refine
            Cmd.BigStep.while_true ?_
              (retag_bigStep_project hExt hF.2) hTail
          exact (pushGuard_eval_down hExt p G hDown).mp
            hEval

end Preprocess

end Whiel

------------------------------------------------------------
-- The Push Lemma, Backward
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  A run of the source loop lifts to a run of the pushed loop
  from any state with the push flag down. Once `p` is down
  no code raises it again, so every iteration is the source
  body.
-/
theorem pushLoop_lift
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (hFresh : p.sym.1 ∉ Δ.syms)
    (G : Guard D Δ)
    (Push B : Cmd D Δ)
    {s t : Instance D Δ}
    (hStep : Cmd.BigStep (.«while» G B) s t) :
    ∀ u : Instance D Ω, project hExt u = s →
      ¬ p.Up u →
      ∃ v : Instance D Ω,
        Cmd.BigStep
            (.«while» (pushGuard hExt p G)
              (pushBody hExt p Push B)) u v ∧
          project hExt v = t ∧ ¬ p.Up v := by
  generalize hW :
      (Cmd.«while» G B : Cmd D Δ) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G' B' s hFalse =>
      cases hW
      intro u hProj hDown
      refine
        ⟨u, Cmd.BigStep.while_false ?_, hProj, hDown⟩
      intro hEval
      refine hFalse ?_
      rw [← hProj]
      exact (pushGuard_eval_down hExt p G hDown).mp hEval
  | @while_true G' B' s y t hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      intro u hProj hDown
      rcases retag_bigStep_lift hExt hProj hRun with
        ⟨m, hRunΩ, hProjM⟩
      have hDownM : ¬ p.Up m :=
        hoist_down_pres hExt hFresh B u m hDown hRunΩ
      rcases ihLoop rfl m hProjM hDownM with
        ⟨v, hV, hProjV, hDownV⟩
      refine ⟨v, ?_, hProjV, hDownV⟩
      refine Cmd.BigStep.while_true ?_ ?_ hV
      · refine (pushGuard_eval_down hExt p G hDown).mpr ?_
        rw [hProj]
        exact hEval
      · exact Cmd.BigStep.ite_false hDown hRunΩ

end Preprocess

end Whiel

------------------------------------------------------------
-- The Push Lemma
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  Lemma "Push": the pushed framed loop is equivalent modulo
  the push flag to the original one, in the arbitrary-start
  form. The prefix runs the kept part and raises `p`, so by
  the flag-initialization principle the loop is entered with
  `p` up whatever the initial flags were; the first
  iteration then runs the pushed part and lowers `p`, and
  from that point the guard is the source guard and the body
  is the source body.
-/
theorem pushFramed_equivMod
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (hFresh : p.sym.1 ∉ Δ.syms)
    (Keep Push : Cmd D Δ)
    (L : Framed D Δ)
    (hInit :
      Cmd.BigStepEquiv L.init (.seq Keep Push)) :
    EquivMod hExt L.unfold
      (pushFramed hExt p Keep Push L).unfold := by
  constructor
  · intro s t hRun
    rcases (Framed.bigStep_unfold_iff L _ t).mp hRun with
      ⟨a, b, hInitRun, hLoop, hClose⟩
    rcases
      (Cmd.bigStep_seq_iff _ _ _ a).mp
        ((hInit _ a).mp hInitRun) with
      ⟨k, hKeep, hPush⟩
    rcases retag_bigStep_lift hExt rfl hKeep with
      ⟨m, hKeepΩ, hProjM⟩
    set m₁ := Instance.update m p.sym (p.topExpr.eval m)
      with hm₁
    have hRaise : Cmd.BigStep p.raise m m₁ :=
      Cmd.BigStep.assign m p.sym p.topExpr
    have hUpOne : p.Up m₁ :=
      FlagSym.up_of_bigStep_raise hRaise
    have hProjOne : project hExt m₁ = k := by
      rw [project_of_bigStep_raise hExt hFresh hRaise,
        hProjM]
    rcases retag_bigStep_lift hExt hProjOne hPush with
      ⟨m₂, hPushΩ, hProjTwo⟩
    set m₃ :=
      Instance.update m₂ p.sym (p.emptyExpr.eval m₂)
      with hm₃
    have hLower : Cmd.BigStep p.lower m₂ m₃ :=
      Cmd.BigStep.assign m₂ p.sym p.emptyExpr
    have hDownThree : ¬ p.Up m₃ :=
      FlagSym.not_up_of_bigStep_lower hLower
    have hProjThree : project hExt m₃ = a := by
      rw [project_of_bigStep_lower hExt hFresh hLower,
        hProjTwo]
    rcases
      pushLoop_lift hExt p hFresh L.guard Push L.body
        hLoop m₃ hProjThree hDownThree with
      ⟨v, hV, hProjV, hDownV⟩
    rcases retag_bigStep_lift hExt hProjV hClose with
      ⟨w, hCloseΩ, hProjW⟩
    refine ⟨w, ?_, hProjW⟩
    refine
      (Framed.bigStep_unfold_iff _ s w).mpr
        ⟨m₁, v, Cmd.BigStep.seq hKeepΩ hRaise, ?_,
          hCloseΩ⟩
    refine
      Cmd.BigStep.while_true
        (pushGuard_of_up hExt p L.guard hUpOne) ?_ hV
    exact
      Cmd.BigStep.ite_true hUpOne
        (Cmd.BigStep.seq hPushΩ hLower)
  · intro s t' hRun
    rcases (Framed.bigStep_unfold_iff _ s t').mp hRun with
      ⟨u, v, hInitRun, hLoop, hClose⟩
    rcases flagInit_raise hExt hFresh hInitRun with
      ⟨hUp, hKeepRun⟩
    rcases
      (pushLoop_project hExt p hFresh L.guard Push L.body
        hLoop).1 hUp with ⟨hTail, _⟩
    rcases (Cmd.bigStep_seq_iff _ _ _ _).mp hTail with
      ⟨a, hPushRun, hLoopRun⟩
    refine
      (Framed.bigStep_unfold_iff L _ _).mpr
        ⟨a, project hExt v, ?_, hLoopRun,
          retag_bigStep_project hExt hClose⟩
    exact
      (hInit _ a).mpr
        (Cmd.BigStep.seq hKeepRun hPushRun)

/-
  The exit clause of Lemma "Push": the push flag is down at
  every terminal state of the pushed loop, reached from any
  initial state.
-/
theorem pushFramed_flag_down
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (hFresh : p.sym.1 ∉ Δ.syms)
    (Keep Push : Cmd D Δ)
    (L : Framed D Δ)
    {u v : Instance D Ω}
    (hLoop :
      Cmd.BigStep
        (.«while» (pushFramed hExt p Keep Push L).guard
          (pushFramed hExt p Keep Push L).body) u v) :
    ¬ p.Up v := by
  by_cases hUp : p.Up u
  · exact
      ((pushLoop_project hExt p hFresh L.guard Push L.body
        hLoop).1 hUp).2
  · exact
      ((pushLoop_project hExt p hFresh L.guard Push L.body
        hLoop).2 hUp).2

/- The push keeps the loop-free components loop-free. -/
theorem pushFramed_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    {Keep Push : Cmd D Δ}
    {L : Framed D Δ}
    (hKeep : LoopFree Keep)
    (hPush : LoopFree Push)
    (hParts : L.LoopFreeParts) :
    (pushFramed hExt p Keep Push L).LoopFreeParts := by
  obtain ⟨hInit, hBody, hClose⟩ := hParts
  refine ⟨?_, ?_, loopFree_of_retag hExt hClose⟩
  · refine (loopFree_seq_iff _ _).mpr ?_
    exact ⟨loopFree_of_retag hExt hKeep, rfl⟩
  · refine
      (loopFree_ite_iff _ _ _).mpr ⟨?_, ?_⟩
    · refine (loopFree_seq_iff _ _).mpr ?_
      exact ⟨loopFree_of_retag hExt hPush, rfl⟩
    · exact loopFree_of_retag hExt hBody

end Preprocess

end Whiel

------------------------------------------------------------
-- The Loop-Head Fixed Point
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Lemma "Loop-head fixed point": where the quantifier-free
  strongest postcondition is defined, every state satisfying
  it satisfies the source assertion and is a fixed point of
  the command. Both clauses are the repository's
  `spLoopFreeNoFresh?_eval_imp_fixed`, named here in the
  note's vocabulary.
-/
theorem loopHead_fixed
    {C : Cmd D Γ}
    (hFree : C.LoopFree)
    {pre post : AssertExpr D Γ}
    (hSP :
      AssertExpr.spLoopFreeNoFresh? C hFree pre =
        some post)
    {u : Instance D Γ}
    (hEval : post.eval u) :
    pre.eval u ∧ Cmd.BigStep C u u :=
  AssertExpr.spLoopFreeNoFresh?_eval_imp_fixed C hFree pre
    post hSP u hEval

/-
  The exactness clause of Definition "Quantifier-free
  strongest postcondition": where defined, it is the
  strongest postcondition and not merely an entailed
  consequence of it.
-/
theorem loopHead_exact
    {C : Cmd D Γ}
    (hFree : C.LoopFree)
    {pre post : AssertExpr D Γ}
    (hSP :
      AssertExpr.spLoopFreeNoFresh? C hFree pre =
        some post)
    (u : Instance D Γ) :
    post.eval u ↔ Hoare.sp C pre.eval u :=
  AssertExpr.spLoopFreeNoFresh?_eval_iff C hFree pre post
    hSP u

/-
  The quantifier-free strongest postcondition of a
  quantifier-free assertion is quantifier-free.
-/
theorem loopHead_noBoundSymbols
    {C : Cmd D Γ}
    (hFree : C.LoopFree)
    {pre post : AssertExpr D Γ}
    (hSP :
      AssertExpr.spLoopFreeNoFresh? C hFree pre =
        some post)
    (hPre : pre.NoBoundSymbols) :
    post.NoBoundSymbols :=
  AssertExpr.spLoopFreeNoFresh?_noBoundSymbols C hFree pre
    post hSP hPre

end Preprocess

end Whiel

------------------------------------------------------------
-- The Loop-Head Assertion Of The Push
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ Ω : UnnamedSchema A}

/-
  The split keeps a quantifier-free assertion
  quantifier-free: each step is the repository's
  quantifier-free strongest postcondition, which introduces
  no relation symbol.
-/
theorem splitItems_mid_noBoundSymbols
    (items : List (Cmd D Γ))
    {φ : AssertExpr D Γ}
    (hNo : φ.NoBoundSymbols) :
    (splitItems items φ).mid.NoBoundSymbols := by
  induction items generalizing φ with
  | nil => exact hNo
  | cons I rest ih =>
      rw [splitItems]
      by_cases hFree : LoopFree I
      · rw [dif_pos hFree]
        cases hSP :
            AssertExpr.spLoopFreeNoFresh? I
              (cmdLoopFree_of_loopFree hFree) φ with
        | none => exact hNo
        | some ψ =>
            exact
              ih
                (loopHead_noBoundSymbols
                  (cmdLoopFree_of_loopFree hFree) hSP hNo)
      · rw [dif_neg hFree]
        exact hNo

/-
  `pre' = φ_m ∧ p` of Definition "Preamble push", read over
  the extended schema: the kept part's strongest
  postcondition, retagged, conjoined with the push flag.
-/
def pushedPre
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (mid : AssertExpr D Δ)
    (hNo : mid.NoBoundSymbols) :
    AssertExpr D Ω :=
  AssertExpr.ofQF
    (QFAssertExpr.and
      ((mid.toQFOfNoBound hNo).onExtension hExt)
      p.test)

/- The pushed loop head is quantifier-free. -/
theorem pushedPre_noBoundSymbols
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (mid : AssertExpr D Δ)
    (hNo : mid.NoBoundSymbols) :
    (pushedPre hExt p mid hNo).NoBoundSymbols :=
  AssertExpr.ofQF_noBound _

/- The pushed loop head says exactly `φ_m` and `p` up. -/
theorem pushedPre_eval_iff
    (hExt : Ω.extensionOf Δ)
    (p : FlagSym Ω)
    (mid : AssertExpr D Δ)
    (hNo : mid.NoBoundSymbols)
    (I : Instance D Ω) :
    (pushedPre hExt p mid hNo).eval I ↔
      (mid.eval (project hExt I) ∧ p.Up I) := by
  have hMidIff :
      Guard.eval
          (QFAssertExpr.onExtension hExt
            (mid.toQFOfNoBound hNo)) I ↔
        mid.eval (project hExt I) :=
    Iff.trans
      (retag_eval_iff hExt (mid.toQFOfNoBound hNo) I)
      (AssertExpr.toQFOfNoBound_eval_iff mid hNo
        (project hExt I))
  rw [pushedPre, AssertExpr.ofQF_eval_iff]
  constructor
  · rintro ⟨hMid, hFlag⟩
    exact ⟨hMidIff.mp hMid, hFlag⟩
  · rintro ⟨hMid, hFlag⟩
    exact ⟨hMidIff.mpr hMid, hFlag⟩

end Preprocess

end Whiel

------------------------------------------------------------
-- The Preprocessed Triple
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/-
  The framed loop the preprocessor finally returns, over the
  flag extension the whole transformation draws, together
  with the loop-head assertion of the single-loop triple.
-/
structure Preprocessed
    (D : Type) [Domain D]
    (Γ : UnnamedSchema ProgramNames) : Type where
  ids : List Nat
  loop : Framed D (flagExt Γ ids)
  pre : AssertExpr D (flagExt Γ ids)

/- The precondition, read over the normalizer's schema. -/
def normalizedPre
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    AssertExpr D (flagExt Γ (normalize C).ids) :=
  retagAssert (flagExt_extensionOf Γ (normalize C).ids)
    pre hNo

/- The split of the cleaned prefix against it. -/
def normalizedSplit
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    PreambleSplit D (flagExt Γ (normalize C).ids) :=
  splitItems (seqItems (normalize C).loop.init)
    (normalizedPre C pre hNo)

/-
  The push identifier as a nullary symbol of the extended
  schema. The supply is a counter, so it is the seed plus
  the budget, and it is fresh both for the input schema and
  for every identifier the recursion drew.
-/
def pushFlag
    (C : Cmd D Γ) :
    FlagSym (flagExt Γ ((normalize C).ids ++
      [normalizeNext C])) :=
  flagSymOf Γ _ (normalizeNext C) (by simp)
    (flagName_normalizeNext_not_mem C)

/-
  The push identifier is fresh for the schema the
  normalizer's output lives over.
-/
theorem pushFlag_fresh
    (C : Cmd D Γ) :
    (pushFlag (D := D) C).sym.1 ∉
      (flagExt Γ (normalize C).ids).syms := by
  rw [pushFlag, flagSymOf_sym_val]
  intro hIn
  rcases Finset.mem_union.mp hIn with h | h
  · exact flagName_normalizeNext_not_mem C h
  · exact normalizeNext_not_mem_ids C
      (mem_flagNames_iff.mp h)

/-
  The whole transformation of the note: normalize, clean,
  then split the preamble and push what obstructs. The push
  is applied once, at the top and last, so the pushed flag
  is the outermost one; when nothing obstructs the framed
  loop and the flag set are unchanged.
-/
def preprocess
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    Preprocessed D Γ :=
  match (normalizedSplit C pre hNo).push with
  | [] =>
      ⟨(normalize C).ids, (normalize C).loop,
        (normalizedSplit C pre hNo).mid⟩
  | pushed =>
      ⟨(normalize C).ids ++ [normalizeNext C],
        pushFramed
          (flagExt_mono Γ (subsetAppendLeft _ _))
          (pushFlag C)
          (seqOfItems (normalizedSplit C pre hNo).keep)
          (seqOfItems pushed)
          (normalize C).loop,
        pushedPre (flagExt_mono Γ (subsetAppendLeft _ _))
          (pushFlag C) (normalizedSplit C pre hNo).mid
          (splitItems_mid_noBoundSymbols _
            (retagAssert_noBoundSymbols _ pre hNo))⟩

end Preprocess

end Whiel

------------------------------------------------------------
-- The Two Cases Of The Preprocessor
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/- When nothing obstructs, the framed loop is unchanged. -/
theorem preprocess_eq_of_no_push
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols)
    (hP : (normalizedSplit C pre hNo).push = []) :
    preprocess C pre hNo =
      ⟨(normalize C).ids, (normalize C).loop,
        (normalizedSplit C pre hNo).mid⟩ := by
  unfold preprocess
  rw [hP]

/- Otherwise the push draws one further identifier. -/
theorem preprocess_eq_of_push
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols)
    {I : Cmd D (flagExt Γ (normalize C).ids)}
    {rest : List (Cmd D (flagExt Γ (normalize C).ids))}
    (hP :
      (normalizedSplit C pre hNo).push = I :: rest) :
    preprocess C pre hNo =
      ⟨(normalize C).ids ++ [normalizeNext C],
        pushFramed
          (flagExt_mono Γ (subsetAppendLeft _ _))
          (pushFlag C)
          (seqOfItems (normalizedSplit C pre hNo).keep)
          (seqOfItems (I :: rest))
          (normalize C).loop,
        pushedPre (flagExt_mono Γ (subsetAppendLeft _ _))
          (pushFlag C) (normalizedSplit C pre hNo).mid
          (splitItems_mid_noBoundSymbols _
            (retagAssert_noBoundSymbols _ pre hNo))⟩ := by
  unfold preprocess
  rw [hP]

/-
  Theorem "Normalization" together with Lemma "Push": every
  command is equivalent modulo the flags the whole
  transformation draws to the unfolding of the framed loop
  the preprocessor returns, in the arbitrary-start form.
-/
theorem preprocess_equivMod
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    EquivMod
      (flagExt_extensionOf Γ (preprocess C pre hNo).ids) C
      (preprocess C pre hNo).loop.unfold := by
  cases hP : (normalizedSplit C pre hNo).push with
  | nil =>
      rw [preprocess_eq_of_no_push C pre hNo hP]
      exact normalize_equivMod C
  | cons I rest =>
      rw [preprocess_eq_of_push C pre hNo hP]
      have hInit :
          Cmd.BigStepEquiv (normalize C).loop.init
            (.seq
              (seqOfItems
                (normalizedSplit C pre hNo).keep)
              (seqOfItems (I :: rest))) := by
        have hSplit :=
          bigStepEquiv_splitItems
            (normalize C).loop.init
            (normalizedPre C pre hNo)
        rw [← hP]
        exact Cmd.BigStepEquiv.symm hSplit
      exact
        EquivMod.compose
          (hΩΔ := flagExt_mono Γ (subsetAppendLeft _ _))
          (normalize_equivMod C)
          (pushFramed_equivMod _ (pushFlag C)
            (pushFlag_fresh C) _ _ _ hInit)

/-
  The exit clause of Lemma "Push" for the preprocessor: when
  a push occurs, the push flag is down at every terminal
  state of the loop, reached from any initial state.
-/
theorem preprocess_push_flag_down
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols)
    {I : Cmd D (flagExt Γ (normalize C).ids)}
    {rest : List (Cmd D (flagExt Γ (normalize C).ids))}
    {u v :
      Instance D
        (flagExt Γ
          ((normalize C).ids ++ [normalizeNext C]))}
    (hLoop :
      Cmd.BigStep
        (.«while»
          (pushFramed
            (flagExt_mono Γ (subsetAppendLeft _ _))
            (pushFlag C)
            (seqOfItems (normalizedSplit C pre hNo).keep)
            (seqOfItems (I :: rest))
            (normalize C).loop).guard
          (pushFramed
            (flagExt_mono Γ (subsetAppendLeft _ _))
            (pushFlag C)
            (seqOfItems (normalizedSplit C pre hNo).keep)
            (seqOfItems (I :: rest))
            (normalize C).loop).body) u v) :
    ¬ (pushFlag C).Up v :=
  pushFramed_flag_down _ (pushFlag C) (pushFlag_fresh C)
    _ _ _ hLoop

/-
  Proposition "Totality, shape, determinism" for the whole
  transformation: the result is a framed loop with loop-free
  components, so its unfolding has exactly one loop.
-/
theorem preprocess_loopFreeParts
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    (preprocess C pre hNo).loop.LoopFreeParts := by
  cases hP : (normalizedSplit C pre hNo).push with
  | nil =>
      rw [preprocess_eq_of_no_push C pre hNo hP]
      exact normalize_loopFreeParts C
  | cons I rest =>
      rw [preprocess_eq_of_push C pre hNo hP]
      have hParts := normalize_loopFreeParts C
      have hItems :
          ∀ J ∈ seqItems (normalize C).loop.init,
            LoopFree J :=
        loopFree_of_mem_seqItems hParts.1
      refine
        pushFramed_loopFreeParts _ _ ?_ ?_ hParts
      · refine loopFree_seqOfItems ?_
        intro J hJ
        exact hItems J (mem_of_mem_splitItems_keep hJ)
      · refine loopFree_seqOfItems ?_
        intro J hJ
        refine
          hItems J
            (mem_of_mem_splitItems_push
              (φ := normalizedPre C pre hNo) ?_)
        rw [normalizedSplit] at hP
        rw [hP]
        exact hJ

theorem loops_preprocess_unfold
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    loops (preprocess C pre hNo).loop.unfold = 1 :=
  Framed.loops_unfold (preprocess_loopFreeParts C pre hNo)

/-
  The loop-head assertion is quantifier-free in both cases
  of the split: without a push it is the repository's
  quantifier-free strongest postcondition of a
  quantifier-free start, and with one it is that assertion
  conjoined with a flag test.
-/
theorem preprocess_pre_noBoundSymbols
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    (preprocess C pre hNo).pre.NoBoundSymbols := by
  cases hP : (normalizedSplit C pre hNo).push with
  | nil =>
      rw [preprocess_eq_of_no_push C pre hNo hP]
      exact splitItems_mid_noBoundSymbols _
        (retagAssert_noBoundSymbols _ pre hNo)
  | cons I rest =>
      rw [preprocess_eq_of_push C pre hNo hP]
      exact pushedPre_noBoundSymbols _ _ _ _

end Preprocess

end Whiel
