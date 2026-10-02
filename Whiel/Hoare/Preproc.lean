-- Author: Jesse Comer
import Whiel.Hoare.Rewrites
import Whiel.Hoare.CounterExample
import Whiel.Preprocess.Transfer

/-
  Stable preprocessing interface for synthesis inputs.

  `Hoare.Preproc` packages the single-loop Hoare triple the
  generic preprocessor of `Whiel/Preprocess/**` derives from
  an input triple, together with the theorems needed to
  return a proof, and a refutation, to the input triple.

  The preprocessed loop no longer lives over the input
  schema. It is a framed loop over the flag extension the
  transformation draws, so the structure carries its own
  output schema and the extension witness that relates it to
  the input schema, and the input-facing statements speak of
  the projection of an output state.

  Main declarations:
    * `Hoare.Preproc`
    * `Hoare.Preproc.loopCmd`
    * `Hoare.Preproc.framedCmd`
    * `Hoare.Preproc.sourcePrefixInitVC`
    * `Hoare.Preproc.loopOnlyInitValid_of_sourcePrefixInitValid`
    * same-input counterexample reconstruction
    * `Hoare.Preproc.valid_input`
    * `Hoare.ofPreprocessed`
    * `Hoare.preprocessOf` and `Hoare.preprocessWithSupply`
      (the legacy framed-loop constructor)

  Correctness is inherited: `valid_of_loop` is Theorem
  "Transfer" and `refutation_of_loop` is Corollary
  "Refutation transfer", both of
  `Whiel/Preprocess/Transfer.lean`, applied here.
-/

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

open AssertExpr

/-
  A preprocessed single-loop triple derived from an input
  Hoare triple.

  The loop, its head assertion, its closing assertion, and
  the loop-free code framing it all live over `outSchema`,
  an extension of the input schema by the flag relations the
  transformation drew. `outExtends` is the only bridge back:
  every statement about the input triple reads an output
  state through its projection.
-/
structure Preproc
    (inputPre : AssertExpr D Γ)
    (inputCmd : Cmd D Γ)
    (inputPost : AssertExpr D Γ) where
  outSchema : UnnamedSchema A
  outExtends : outSchema.extensionOf Γ
  loopPre : AssertExpr D outSchema
  loopGuard : Guard D outSchema
  loopBody : Cmd D outSchema
  loopBody_loopFree : loopBody.LoopFree
  loopPost : AssertExpr D outSchema
  loopPre_noBound : loopPre.NoBoundSymbols
  loopPost_noBound : loopPost.NoBoundSymbols
  sourcePrefix : Cmd D outSchema
  sourcePrefix_loopFree : sourcePrefix.LoopFree
  sourceClose : Cmd D outSchema
  sourceClose_loopFree : sourceClose.LoopFree
  loopPre_source_reaches :
    forall (s : Instance D Γ) (u : Instance D outSchema),
      inputPre.eval s ->
        Cmd.BigStep sourcePrefix
            (Preprocess.lift outExtends s) u ->
          loopPre.eval u
  loopPre_source_fixed :
    forall u : Instance D outSchema,
      loopPre.eval u ->
        inputPre.eval (Preprocess.project outExtends u) ∧
          Cmd.BigStep sourcePrefix u u
  valid_of_loop :
    HoareValid loopPre (.while loopGuard loopBody) loopPost →
      HoareValid inputPre inputCmd inputPost
  refutation_of_loop :
    forall u v : Instance D outSchema,
      loopPre.eval u ->
        Cmd.BigStep (.while loopGuard loopBody) u v ->
          ¬ loopPost.eval v ->
            ∃ K : Instance D Γ,
              counterExample inputPre inputCmd inputPost
                (Preprocess.project outExtends u) K

namespace Preproc

/- The loop-only command produced by preprocessing. -/
def loopCmd
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost) :
    Cmd D P.outSchema :=
  .while P.loopGuard P.loopBody

/-
  The whole framed loop `P; while G do B end; S` the
  preprocessor produced, over the flag extension.
-/
def framedCmd
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost) :
    Cmd D P.outSchema :=
  .seq P.sourcePrefix (.seq P.loopCmd P.sourceClose)

/-
  Initialization at the post-split prefix, expressed using
  its exact loop-free weakest precondition. The input
  precondition is read over the extended schema; it is
  quantifier-free, so the reading is the note's retagging.
-/
def sourcePrefixInitVC
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost)
    (hNoPre : inputPre.NoBoundSymbols)
    (inv : AssertExpr D P.outSchema) :
    AssertExpr.Entailment D P.outSchema where
  lhs := Preprocess.retagAssert P.outExtends inputPre hNoPre
  rhs :=
    AssertExpr.wpLoopFree P.sourcePrefix
      P.sourcePrefix_loopFree inv

/- The source-prefix initialization obligation is valid. -/
def sourcePrefixInitValid
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost)
    (hNoPre : inputPre.NoBoundSymbols)
    (inv : AssertExpr D P.outSchema) : Prop :=
  (P.sourcePrefixInitVC hNoPre inv).Valid

/-
  No invariant is lost by checking initialization at the
  loop head instead of at the source prefix: a loop-head
  state is a fixed point of the prefix and satisfies the
  input precondition on its projection, so the prefix
  obligation implies the loop-head obligation.

  The converse direction of the old framed-loop bridge is
  not restated here. It rested on the loop-head assertion
  being the exact strongest postcondition of the prefix from
  the input precondition, which the preamble push replaces
  by the two clauses above: the loop head is reached from
  every lifted start (`loopPre_source_reaches`) and is fixed
  by the prefix (`loopPre_source_fixed`).
-/
theorem loopOnlyInitValid_of_sourcePrefixInitValid
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost)
    (hNoPre : inputPre.NoBoundSymbols)
    (inv : AssertExpr D P.outSchema)
    (hSource : P.sourcePrefixInitValid hNoPre inv) :
    loopOnlyInitValid P.loopPre inv := by
  intro u hLoopPre
  rcases P.loopPre_source_fixed u hLoopPre with
    ⟨hPre, hFixed⟩
  have hRetag :
      (Preprocess.retagAssert P.outExtends inputPre
        hNoPre).eval u :=
    (Preprocess.retag_assert_eval_iff P.outExtends inputPre
      hNoPre u).mpr hPre
  have hWP :
      (AssertExpr.wpLoopFree P.sourcePrefix
        P.sourcePrefix_loopFree inv).eval u :=
    hSource u hRetag
  exact
    Hoare.wpLoopFree_valid P.sourcePrefix
      P.sourcePrefix_loopFree inv u u hWP hFixed

/-
  A loop-head state projects to an original input state
  fixed by the post-split prefix. This supplies the
  same-input reconstruction used by CEX certification.
-/
theorem loopPre_eval_imp_sourcePrefix_fixed
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost)
    (J : Instance D P.outSchema)
    (hEval : P.loopPre.eval J) :
    inputPre.eval (Preprocess.project P.outExtends J) ∧
      Cmd.BigStep P.sourcePrefix J J :=
  P.loopPre_source_fixed J hEval

/-
  A loop-only counterexample starting at a loop-head state
  reconstructs a source counterexample starting at that
  state's projection.
-/
theorem counterExample_input_of_loop_counterExample
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost)
    (I J : Instance D P.outSchema)
    (hCounterExample :
      counterExample P.loopPre P.loopCmd P.loopPost I J) :
    ∃ K,
      counterExample inputPre inputCmd inputPost
        (Preprocess.project P.outExtends I) K :=
  P.refutation_of_loop I J hCounterExample.1
    hCounterExample.2.1 hCounterExample.2.2

/-
  A proof of the preprocessed triple proves the input
  triple.
-/
theorem valid_input
    {inputPre : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    {inputPost : AssertExpr D Γ}
    (P : Preproc inputPre inputCmd inputPost)
    (hLoop :
      HoareValid P.loopPre P.loopCmd P.loopPost) :
    HoareValid inputPre inputCmd inputPost :=
  P.valid_of_loop hLoop

end Preproc

end Hoare

end Whiel

------------------------------------------------------------
-- The Bridge To The Generic Preprocessor
------------------------------------------------------------

namespace Whiel

namespace Hoare

open Concrete
open Preprocess

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/-
  The bridge: the generic preprocessor's output, packaged as
  the synthesis layer's `Preproc`.

  Every proof obligation of the structure is discharged by a
  named result of `Whiel/Preprocess/**` at this one site:
  the shape by Proposition "Totality, shape, determinism",
  the loop head by Lemma "Loop-head fixed point" and the
  split's own reachability clause, the soundness by Theorem
  "Transfer", and the counterexample by Corollary
  "Refutation transfer". Nothing is re-proved here.
-/
def ofPreprocessed
    (inputPre : AssertExpr D Γ)
    (inputCmd : Cmd D Γ)
    (inputPost : AssertExpr D Γ)
    (hNoPre : inputPre.NoBoundSymbols)
    (hNoPost : inputPost.NoBoundSymbols) :
    Preproc inputPre inputCmd inputPost where
  outSchema :=
    flagExt Γ (preprocess inputCmd inputPre hNoPre).ids
  outExtends :=
    flagExt_extensionOf Γ
      (preprocess inputCmd inputPre hNoPre).ids
  loopPre := (preprocess inputCmd inputPre hNoPre).pre
  loopGuard :=
    (preprocess inputCmd inputPre hNoPre).loop.guard
  loopBody :=
    (preprocess inputCmd inputPre hNoPre).loop.body
  loopBody_loopFree :=
    cmdLoopFree_of_loopFree
      (preprocess_loopFreeParts inputCmd inputPre
        hNoPre).2.1
  loopPost :=
    closingAssertion _ (preprocess inputCmd inputPre hNoPre).loop
      (preprocess_close_loopFree inputCmd inputPre hNoPre)
      inputPost hNoPost
  loopPre_noBound :=
    preprocess_pre_noBoundSymbols inputCmd inputPre hNoPre
  loopPost_noBound :=
    closingAssertion_noBoundSymbols _ _ _ _ _
  sourcePrefix :=
    (preprocess inputCmd inputPre hNoPre).loop.init
  sourcePrefix_loopFree :=
    cmdLoopFree_of_loopFree
      (preprocess_loopFreeParts inputCmd inputPre hNoPre).1
  sourceClose :=
    (preprocess inputCmd inputPre hNoPre).loop.close
  sourceClose_loopFree :=
    preprocess_close_loopFree inputCmd inputPre hNoPre
  loopPre_source_reaches :=
    preprocess_loopHead inputCmd inputPre hNoPre
  loopPre_source_fixed :=
    preprocess_loopHead_fixed inputCmd inputPre hNoPre
  valid_of_loop := fun hLoop =>
    preprocess_transfer inputCmd inputPre inputPost hNoPre
      hNoPost hLoop
  refutation_of_loop := by
    intro u v hHead hLoop hFail
    rcases
        preprocess_refutation inputCmd inputPre inputPost
          hNoPre hNoPost hHead hLoop hFail with
      ⟨hPre, K, hRun, hPost⟩
    exact ⟨K, hPre, hRun, hPost⟩

end Hoare

end Whiel

------------------------------------------------------------
-- The Legacy Framed-Loop Constructor
------------------------------------------------------------

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

open AssertExpr

/-
  The reflexive extension is the identity on states, so a
  preprocessing result that draws no flag speaks about the
  input schema directly.
-/
theorem project_extensionOf_refl
    (I : Instance D Γ) :
    Preprocess.project (UnnamedSchema.extensionOf_refl Γ)
        I = I := by
  apply Instance.ext
  intro X
  unfold Preprocess.project Instance.reduct
  simp

theorem lift_extensionOf_refl
    (I : Instance D Γ) :
    Preprocess.lift (UnnamedSchema.extensionOf_refl Γ)
        I = I := by
  apply Instance.ext
  intro X
  unfold Preprocess.lift Instance.expandEmpty
    Instance.relationOfExtension
  simp [X.2]

end Hoare

end Whiel

namespace Whiel

namespace Hoare

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

open AssertExpr

private theorem not_framed_of_none
    {C : Cmd D Γ}
    (hParts : C.framedLoopParts? = none)
    (hFramed : C.FramedLoop) :
    False := by
  rcases hFramed with ⟨Init, G, Body, Close, hSome⟩
  rw [hParts] at hSome
  contradiction

/-
  The precondition computed by framed-loop preprocessing.
-/
def preprocessLoopPreOf
    (inputPre : AssertExpr D Γ)
    (inputCmd : Cmd D Γ)
    (_inputPost : AssertExpr D Γ)
    (hFramed : inputCmd.FramedLoop) :
    AssertExpr D Γ :=
  match hParts : inputCmd.framedLoopParts? with
  | none =>
      False.elim (not_framed_of_none hParts hFramed)
  | some (Init, _G, _Body, _Close) =>
      let hSound := Cmd.framedLoopParts?_sound hParts
      AssertExpr.framedLoopPre Init hSound.1.1 inputPre

/-
  The postcondition computed by framed-loop preprocessing.
-/
def preprocessLoopPostOf
    (_inputPre : AssertExpr D Γ)
    (inputCmd : Cmd D Γ)
    (inputPost : AssertExpr D Γ)
    (hFramed : inputCmd.FramedLoop) :
    AssertExpr D Γ :=
  match hParts : inputCmd.framedLoopParts? with
  | none =>
      False.elim (not_framed_of_none hParts hFramed)
  | some (_Init, _G, _Body, Close) =>
      let hSound := Cmd.framedLoopParts?_sound hParts
      AssertExpr.framedLoopPost Close hSound.2.2.1 inputPost

/-
  The legacy constructor, for a source that is already a
  framed loop over a carrier with a fresh-name supply. It
  draws no flag, so its output schema is the input schema
  and its extension witness is the reflexive one; the
  generic preprocessor of `Whiel/Preprocess/**` supersedes
  it on the production `ProgramNames` path.
-/
def preprocessOf
    (inputPre : AssertExpr D Γ)
    (inputCmd : Cmd D Γ)
    (inputPost : AssertExpr D Γ)
    (hFramed : inputCmd.FramedLoop)
    (hLoopPreNoBound :
      (preprocessLoopPreOf inputPre inputCmd inputPost
        hFramed).NoBoundSymbols)
    (hLoopPostNoBound :
      (preprocessLoopPostOf inputPre inputCmd inputPost
        hFramed).NoBoundSymbols) :
    Preproc inputPre inputCmd inputPost :=
  match hParts : inputCmd.framedLoopParts? with
  | none =>
      False.elim (not_framed_of_none hParts hFramed)
  | some (Init, G, Body, Close) =>
      let hSound := Cmd.framedLoopParts?_sound hParts
      let hInit : Init.LoopFree := hSound.1.1
      let hBody : Body.LoopFree := hSound.2.1
      let hClose : Close.LoopFree := hSound.2.2.1
      let loopPre :=
        AssertExpr.spLoopFree Init hInit inputPre
      let loopPost :=
        AssertExpr.wpLoopFree Close hClose inputPost
      have hLoopPreEq :
          preprocessLoopPreOf inputPre inputCmd inputPost
              hFramed =
            loopPre := by
        unfold preprocessLoopPreOf
        split
        · rename_i hNone
          rw [hParts] at hNone
          contradiction
        · rename_i Init' G' Body' Close' hSome
          have hEq :
              some (Init', G', Body', Close') =
                some (Init, G, Body, Close) :=
            hSome.symm.trans hParts
          cases hEq
          rfl
      have hPreNoBound : loopPre.NoBoundSymbols :=
        hLoopPreEq ▸ hLoopPreNoBound
      { outSchema := Γ
        outExtends := UnnamedSchema.extensionOf_refl Γ
        loopPre := loopPre
        loopGuard := G
        loopBody := Body
        loopBody_loopFree := hBody
        loopPost := loopPost
        loopPre_noBound := hPreNoBound
        loopPost_noBound := by
          have hEq :
              preprocessLoopPostOf inputPre inputCmd
                  inputPost hFramed =
                loopPost := by
            unfold preprocessLoopPostOf
            split
            · rename_i hNone
              rw [hParts] at hNone
              contradiction
            · rename_i Init' G' Body' Close' hSome
              have hEq' :
                  some (Init', G', Body', Close') =
                    some (Init, G, Body, Close) :=
                hSome.symm.trans hParts
              cases hEq'
              rfl
          exact hEq ▸ hLoopPostNoBound
        sourcePrefix := Init
        sourcePrefix_loopFree := hInit
        sourceClose := Close
        sourceClose_loopFree := hClose
        loopPre_source_reaches := by
          intro s u hPre hStep
          rw [lift_extensionOf_refl] at hStep
          exact
            (AssertExpr.spLoopFree_eval_iff
              Init hInit inputPre u).mpr ⟨s, hPre, hStep⟩
        loopPre_source_fixed := by
          intro u hEval
          rw [project_extensionOf_refl]
          exact
            AssertExpr.spLoopFree_eval_imp_fixed
              Init hInit inputPre u hPreNoBound hEval
        valid_of_loop := by
          intro hLoop
          exact
            hoareValid_framedLoopParts?_of_loopOnly
              inputPre inputPost hParts hLoop
        refutation_of_loop := by
          intro u v hLoopPre hLoopStep hNotLoopPost
          rw [project_extensionOf_refl]
          have hPrefix :=
            AssertExpr.spLoopFree_eval_imp_fixed
              Init hInit inputPre u hPreNoBound hLoopPre
          rcases
              Cmd.BigStep.exists_of_loopFree
                Close hClose v with
            ⟨K, hCloseStep⟩
          have hNotCloseWP :
              ¬Hoare.wp Close inputPost.eval v := by
            intro hCloseWP
            exact hNotLoopPost
              ((AssertExpr.wpLoopFree_eval_iff
                Close hClose inputPost v).mpr hCloseWP)
          have hNotPost : ¬inputPost.eval K := by
            intro hPost
            apply hNotCloseWP
            intro L hOther
            rw [← Cmd.BigStep.deterministic hCloseStep hOther]
            exact hPost
          have hFramedStep :
              Cmd.BigStep
                (Cmd.framedLoopCommand Init G Body Close)
                u K := by
            unfold Cmd.framedLoopCommand
            apply Cmd.BigStep.seq
            · exact Cmd.BigStep.seq hPrefix.2 hLoopStep
            · exact hCloseStep
          exact
            ⟨K, hPrefix.1,
              ((Cmd.framedLoopParts?_sound hParts).2.2.2
                u K).2 hFramedStep,
              hNotPost⟩ }

/-
  Construct supply-based preprocessing using default proof
  search for the framed-loop checks. This is the legacy
  `IndexAlphaName` entry point; production inputs use
  `Hoare.preprocess` over `ProgramNames`.
-/
def preprocessWithSupply
    (inputPre : AssertExpr D Γ)
    (inputCmd : Cmd D Γ)
    (inputPost : AssertExpr D Γ)
    (hFramed : inputCmd.FramedLoop := by decide)
    (hLoopPreNoBound :
      (preprocessLoopPreOf inputPre inputCmd inputPost
        hFramed).NoBoundSymbols := by decide)
    (hLoopPostNoBound :
      (preprocessLoopPostOf inputPre inputCmd inputPost
        hFramed).NoBoundSymbols := by decide) :
    Preproc inputPre inputCmd inputPost :=
  preprocessOf inputPre inputCmd inputPost
    hFramed hLoopPreNoBound hLoopPostNoBound

end Hoare

end Whiel
