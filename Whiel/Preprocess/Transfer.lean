-- Author: Jesse Comer
import Whiel.Preprocess.Preamble

/-
  The transfer theorem and the refutation corollary.

  The pipeline consumes the single-loop triple over the flag
  extension. This module returns its validity to validity of
  the input triple over the unextended schema, through the
  packaged program of the note's Section 1, and carries a
  refutation back the other way.

  The postcondition side is unconditional: the weakest
  precondition of the loop-free suffix introduces no
  relation symbol, so it preserves the bound-symbol set
  exactly and the closing assertion is quantifier-free
  because the input postcondition is. Only the simulation
  half of the equivalence is used, so the theorem survives
  any future rule that achieves simulation alone.

  Key definitions include:
    * `Whiel.Program.HoareValid`
    * `Whiel.Preprocess.programOfFramed`
    * `Whiel.Preprocess.closingAssertion`

  The refutation carries the witness the note names, not
  merely the invalidity it establishes: its conclusion is
  that the projection of the loop-head state satisfies the
  precondition and runs to a state outside the
  postcondition. The bare `¬ HoareValid` is a one-line
  corollary of each refutation result.

  The main results are:
    * `Whiel.Preprocess.transfer_of_loopHead`
    * `Whiel.Preprocess.preprocess_transfer`
    * `Whiel.Preprocess.preprocess_refutation`
    * `Whiel.Preprocess.preprocess_not_hoareValid`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Hoare Validity For A Program
------------------------------------------------------------

namespace Whiel

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ : UnnamedSchema A}

/-
  Definition "Hoare validity for a program": every
  terminating run of the program from an input satisfying
  the precondition observes an output satisfying the
  postcondition. The assertions speak only of the input and
  output schema, with no reference to flags or an execution
  schema.
-/
def HoareValid
    (pre : AssertExpr D Δ)
    (P : Program D Δ Δ)
    (post : AssertExpr D Δ) : Prop :=
  ∀ s t : Instance D Δ,
    pre.eval s → P.BigStep s t → post.eval t

end Program

end Whiel

------------------------------------------------------------
-- A Framed Loop As A Program
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/-
  A framed loop over an extension of `Γ`, packaged as a
  program with input and output schema `Γ`. The same
  extension witness serves for both, so the program's
  `initialInstance` is the note's lift and its `observe` is
  the note's projection.
-/
def programOfFramed
    (hExt : Ω.extensionOf Γ)
    (L : Framed D Ω) :
    Program D Γ Γ where
  execSchema := Ω
  extendsInput := hExt
  extendsOutput := hExt
  cmd := L.unfold

@[simp] theorem programOfFramed_cmd
    (hExt : Ω.extensionOf Γ)
    (L : Framed D Ω) :
    (programOfFramed hExt L).cmd = L.unfold :=
  rfl

@[simp] theorem programOfFramed_initialInstance
    (hExt : Ω.extensionOf Γ)
    (L : Framed D Ω)
    (I : Instance D Γ) :
    (programOfFramed hExt L).initialInstance I =
      lift hExt I :=
  rfl

@[simp] theorem programOfFramed_observe
    (hExt : Ω.extensionOf Γ)
    (L : Framed D Ω)
    (J : Instance D Ω) :
    (programOfFramed hExt L).observe J = project hExt J :=
  rfl

/-
  Lemma "Program equivalence from lifted starts", for a
  framed loop: an equivalence modulo the flags makes the
  packaged program agree with the source command.
-/
theorem bigStep_programOfFramed_iff
    {hExt : Ω.extensionOf Γ}
    {C : Cmd D Γ}
    {L : Framed D Ω}
    (hEquiv : EquivMod hExt C L.unfold)
    (s t : Instance D Γ) :
    (programOfFramed hExt L).BigStep s t ↔
      Cmd.BigStep C s t := by
  constructor
  · rintro ⟨J, hRun, hObs⟩
    have hProject := hEquiv.projectRun hRun
    rw [programOfFramed_initialInstance,
      project_lift] at hProject
    rw [← hObs]
    exact hProject
  · intro hRun
    rcases
      hEquiv.simulates (lift hExt s) t
        (by rw [project_lift]; exact hRun) with
      ⟨t', hRun', hProj⟩
    exact ⟨t', hRun', hProj⟩

end Preprocess

end Whiel

------------------------------------------------------------
-- The Closing Assertion
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/-
  The postcondition of the single-loop triple: the weakest
  precondition of the loop-free suffix, over the extended
  schema, applied to the retagged input postcondition.
-/
def closingAssertion
    (hExt : Ω.extensionOf Γ)
    (L : Framed D Ω)
    (hClose : L.close.LoopFree)
    (post : AssertExpr D Γ)
    (hNo : post.NoBoundSymbols) :
    AssertExpr D Ω :=
  AssertExpr.wpLoopFree L.close hClose
    (retagAssert hExt post hNo)

/-
  The postcondition side is unconditional: the loop-free
  weakest precondition introduces no relation symbol, so the
  closing assertion is quantifier-free whenever the input
  postcondition is.
-/
theorem closingAssertion_noBoundSymbols
    (hExt : Ω.extensionOf Γ)
    (L : Framed D Ω)
    (hClose : L.close.LoopFree)
    (post : AssertExpr D Γ)
    (hNo : post.NoBoundSymbols) :
    AssertExpr.NoBoundSymbols
      (closingAssertion hExt L hClose post hNo) :=
  AssertExpr.wpLoopFree_noBoundSymbols L.close hClose _
    (retagAssert_noBoundSymbols hExt post hNo)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Transfer Theorem
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/-
  Theorem "Transfer", in the form the two cases of the
  preprocessor instantiate: validity of the single-loop
  triple over the extended schema implies validity of the
  input triple for the packaged program, hence for the
  source command.

  The loop-head hypothesis is what the preamble split
  supplies: every state the prefix reaches from a lifted
  start satisfying the input precondition satisfies the
  loop-head assertion.
-/
theorem transfer_of_loopHead
    (hExt : Ω.extensionOf Γ)
    {L : Framed D Ω}
    (hClose : L.close.LoopFree)
    {pre post : AssertExpr D Γ}
    (hNoPost : post.NoBoundSymbols)
    {pre' : AssertExpr D Ω}
    (hHead :
      ∀ (s : Instance D Γ) (u : Instance D Ω),
        pre.eval s →
          Cmd.BigStep L.init (lift hExt s) u →
            pre'.eval u)
    (hValid :
      HoareValid pre' (.«while» L.guard L.body)
        (closingAssertion hExt L hClose post hNoPost)) :
    Program.HoareValid pre (programOfFramed hExt L) post :=
  by
  rintro s t hPre ⟨J, hRun, hObs⟩
  rw [programOfFramed_cmd,
    programOfFramed_initialInstance] at hRun
  rcases (Framed.bigStep_unfold_iff L _ J).mp hRun with
    ⟨u, v, hInit, hLoop, hClosed⟩
  have hHeadEval : pre'.eval u := hHead s u hPre hInit
  have hMid :
      (closingAssertion hExt L hClose post
        hNoPost).eval v :=
    hValid u v hHeadEval hLoop
  have hPost :
      (retagAssert hExt post hNoPost).eval J :=
    Hoare.wpLoopFree_valid L.close hClose
      (retagAssert hExt post hNoPost) v J hMid hClosed
  rw [← hObs, programOfFramed_observe]
  exact (retag_assert_eval_iff hExt post hNoPost J).mp
    hPost

/-
  The same conclusion at the source command: the packaged
  program agrees with it, so a run of the source is a run of
  the program.
-/
theorem hoareValid_of_transfer
    (hExt : Ω.extensionOf Γ)
    {C : Cmd D Γ}
    {L : Framed D Ω}
    {pre post : AssertExpr D Γ}
    (hEquiv : EquivMod hExt C L.unfold)
    (hProgram :
      Program.HoareValid pre (programOfFramed hExt L)
        post) :
    HoareValid pre.eval C post.eval := by
  intro s t hPre hRun
  exact
    hProgram s t hPre
      ((bigStep_programOfFramed_iff hEquiv s t).mpr hRun)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Refutation Corollary
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/-
  Corollary "Refutation transfer": a loop-head state
  satisfying the loop-head assertion from which the loop
  terminates outside the closing assertion refutes the input
  triple, with witness its own projection.

  The conclusion is the witness itself, as the note states
  it: the projection of the loop-head state satisfies the
  precondition and runs to a state outside the
  postcondition. The bare invalidity of the triple is the
  corollary below.

  The fixed-point clause of Lemma "Loop-head fixed point" is
  what makes the reconstruction constructive: the loop-head
  state is a fixed point of the prefix, so no predecessor
  has to be searched for.
-/
theorem refutation_of_loopHead
    (hExt : Ω.extensionOf Γ)
    {C : Cmd D Γ}
    {L : Framed D Ω}
    (hClose : L.close.LoopFree)
    {pre post : AssertExpr D Γ}
    (hNoPost : post.NoBoundSymbols)
    {pre' : AssertExpr D Ω}
    (hEquiv : EquivMod hExt C L.unfold)
    (hFixed :
      ∀ u : Instance D Ω,
        pre'.eval u →
          pre.eval (project hExt u) ∧
            Cmd.BigStep L.init u u)
    {u' v : Instance D Ω}
    (hHead : pre'.eval u')
    (hLoop :
      Cmd.BigStep (.«while» L.guard L.body) u' v)
    (hFail :
      ¬ (closingAssertion hExt L hClose post
        hNoPost).eval v) :
    pre.eval (project hExt u') ∧
      ∃ t : Instance D Γ,
        Cmd.BigStep C (project hExt u') t ∧
          ¬ post.eval t := by
  rcases hFixed u' hHead with ⟨hPreU, hInit⟩
  have hWp :
      ¬ Hoare.wp L.close
        (retagAssert hExt post hNoPost).eval v := by
    intro hWpEval
    exact hFail
      ((AssertExpr.wpLoopFree_eval_iff L.close hClose
        (retagAssert hExt post hNoPost) v).mpr hWpEval)
  have hWitness :
      ∃ t' : Instance D Ω,
        Cmd.BigStep L.close v t' ∧
          ¬ (retagAssert hExt post hNoPost).eval t' := by
    by_contra hAll
    refine hWp ?_
    intro t' hStep
    by_contra hNot
    exact hAll ⟨t', hStep, hNot⟩
  rcases hWitness with ⟨t', hCloseRun, hNotPost⟩
  have hRun :
      Cmd.BigStep L.unfold u' t' :=
    (Framed.bigStep_unfold_iff L u' t').mpr
      ⟨u', v, hInit, hLoop, hCloseRun⟩
  have hSource :
      Cmd.BigStep C (project hExt u') (project hExt t') :=
    hEquiv.projectRun hRun
  refine ⟨hPreU, project hExt t', hSource, ?_⟩
  intro hPost
  exact hNotPost
    ((retag_assert_eval_iff hExt post hNoPost t').mpr
      hPost)

/-
  Corollary "Refutation transfer", read as the invalidity of
  the input triple: the witness the corollary above returns
  is a counterexample to it.
-/
theorem not_hoareValid_of_loopHead
    (hExt : Ω.extensionOf Γ)
    {C : Cmd D Γ}
    {L : Framed D Ω}
    (hClose : L.close.LoopFree)
    {pre post : AssertExpr D Γ}
    (hNoPost : post.NoBoundSymbols)
    {pre' : AssertExpr D Ω}
    (hEquiv : EquivMod hExt C L.unfold)
    (hFixed :
      ∀ u : Instance D Ω,
        pre'.eval u →
          pre.eval (project hExt u) ∧
            Cmd.BigStep L.init u u)
    {u' v : Instance D Ω}
    (hHead : pre'.eval u')
    (hLoop :
      Cmd.BigStep (.«while» L.guard L.body) u' v)
    (hFail :
      ¬ (closingAssertion hExt L hClose post
        hNoPost).eval v) :
    ¬ HoareValid pre.eval C post.eval := by
  rcases refutation_of_loopHead hExt hClose hNoPost hEquiv
      hFixed hHead hLoop hFail with
    ⟨hPreU, t, hRun, hNotPost⟩
  exact fun hValid => hNotPost (hValid _ _ hPreU hRun)

end Preprocess

end Whiel

------------------------------------------------------------
-- Nested Lifts And Projections
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Δ Ω : UnnamedSchema A}

/-
  Definition "Projection and lift": lifts compose, so
  projecting the outer lift onto the intermediate schema is
  the intermediate lift. Both instances agree on `Γ` and
  send every new relation to the empty one.
-/
theorem project_lift_trans
    (hΔΓ : Δ.extensionOf Γ)
    (hΩΔ : Ω.extensionOf Δ)
    (hΩΓ : Ω.extensionOf Γ)
    (s : Instance D Γ) :
    project hΩΔ (lift hΩΓ s) = lift hΔΓ s := by
  refine eq_of_reduct_eq_of_agree hΔΓ ?_ ?_
  · have hLeft :
        Instance.reduct hΔΓ
            (Instance.reduct hΩΔ (lift hΩΓ s)) =
          Instance.reduct
            (UnnamedSchema.extensionOf_trans hΩΔ hΔΓ)
            (lift hΩΓ s) :=
      Instance.reduct_trans hΩΔ hΔΓ (lift hΩΓ s)
    have hOuter :
        Instance.reduct
            (UnnamedSchema.extensionOf_trans hΩΔ hΔΓ)
            (lift hΩΓ s) = s :=
      project_lift
        (UnnamedSchema.extensionOf_trans hΩΔ hΔΓ) s
    have hRight :
        Instance.reduct hΔΓ (lift hΔΓ s) = s :=
      project_lift hΔΓ s
    unfold project at *
    rw [hLeft, hOuter, hRight]
  · intro X hX
    have hRight : lift hΔΓ s X = ∅ :=
      lift_eq_empty_of_not_mem hΔΓ s X hX
    have hOuter :
        lift hΩΓ s ⟨X.1, hΩΔ.1 X.2⟩ = ∅ :=
      lift_eq_empty_of_not_mem hΩΓ s _ hX
    rw [hRight]
    unfold project Instance.reduct
    simp only [hOuter]
    exact
      FlagSym.cast_empty
        (UnnamedSchema.arity_eq_of_extensionOf hΩΔ X)

/-
  Raising a flag that is already up is the identity, so a
  loop-head state satisfying the pushed assertion is a fixed
  point of the raise.
-/
theorem bigStep_raise_self_of_up
    {p : FlagSym Ω}
    {u : Instance D Ω}
    (hUp : p.Up u) :
    Cmd.BigStep p.raise u u := by
  have hValue : p.topExpr.eval u = u p.sym := by
    rw [FlagSym.eval_topExpr]
    exact
      ((FlagSym.eq_cast_top_iff_ne_empty p.arityZero
        (u p.sym)).mpr
        ((FlagSym.up_iff p u).mp hUp)).symm
  refine (FlagSym.bigStep_raise_iff p u u).mpr ?_
  rw [hValue, Instance.update_cancel]

/-
  A retagged command that is a fixed point on the projection
  is a fixed point on the nose: it leaves every new relation
  alone, and its projection returns.
-/
theorem bigStep_retag_self_of_project_self
    (hExt : Ω.extensionOf Δ)
    {Q : Cmd D Δ}
    {u : Instance D Ω}
    (hRun :
      Cmd.BigStep Q (project hExt u)
        (project hExt u)) :
    Cmd.BigStep (retag hExt Q) u u := by
  rcases retag_bigStep_lift hExt rfl hRun with
    ⟨m, hRunΩ, hProjM⟩
  have hEq : m = u := by
    refine eq_of_reduct_eq_of_agree hExt ?_ ?_
    · exact hProjM
    · intro X hX
      exact retag_preserves_new hExt hRunΩ X hX
  subst hEq
  exact hRunΩ

end Preprocess

end Whiel

------------------------------------------------------------
-- The Loop Head Of The Preprocessor
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/-
  The kept part of the split, as one loop-free command over
  the normalizer's schema.
-/
def keptPrefix
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    Cmd D (flagExt Γ (normalize C).ids) :=
  seqOfItems (normalizedSplit C pre hNo).keep

theorem keptPrefix_loopFree
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    (keptPrefix C pre hNo).LoopFree := by
  refine cmdLoopFree_of_loopFree ?_
  refine loopFree_seqOfItems ?_
  intro J hJ
  exact
    loopFree_of_mem_seqItems (normalize_loopFreeParts C).1
      J (mem_of_mem_splitItems_keep hJ)

/-
  Definition "Quantifier-free strongest postcondition" on
  the kept part: the split's assertion is exactly its
  strongest postcondition through the retagged input
  precondition.
-/
theorem keptPrefix_sp
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    AssertExpr.spLoopFreeNoFresh? (keptPrefix C pre hNo)
        (keptPrefix_loopFree C pre hNo)
        (normalizedPre C pre hNo) =
      some (normalizedSplit C pre hNo).mid :=
  splitItems_keep_sp _ _ _

/-
  With nothing pushed, the kept part is the whole prefix, so
  it runs exactly as the framed loop's prefix.
-/
theorem bigStepEquiv_keptPrefix_of_no_push
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols)
    (hP : (normalizedSplit C pre hNo).push = []) :
    Cmd.BigStepEquiv (keptPrefix C pre hNo)
      (normalize C).loop.init := by
  have hSplit :
      Cmd.BigStepEquiv
        (.seq
          (seqOfItems (normalizedSplit C pre hNo).keep)
          (seqOfItems (normalizedSplit C pre hNo).push))
        (normalize C).loop.init :=
    bigStepEquiv_splitItems (normalize C).loop.init
      (normalizedPre C pre hNo)
  intro I J
  refine Iff.trans ?_ (hSplit I J)
  have hPush :
      seqOfItems (normalizedSplit C pre hNo).push =
        (.skip : Cmd D (flagExt Γ (normalize C).ids)) := by
    rw [hP]
    rfl
  rw [keptPrefix, hPush]
  exact (bigStep_seq_skip_right_iff _ I J).symm

end Preprocess

end Whiel

------------------------------------------------------------
-- Transfer For The Preprocessor, No Push
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/-
  The loop-head hypothesis when nothing is pushed:
  `pre' = φ_k` is the exact strongest postcondition of the
  precondition through the whole prefix.
-/
theorem loopHead_of_no_push
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols)
    (hP : (normalizedSplit C pre hNo).push = [])
    (s : Instance D Γ)
    (u : Instance D (flagExt Γ (normalize C).ids))
    (hPre : pre.eval s)
    (hInit :
      Cmd.BigStep (normalize C).loop.init
        (lift (flagExt_extensionOf Γ (normalize C).ids) s)
        u) :
    (normalizedSplit C pre hNo).mid.eval u := by
  refine
    (loopHead_exact (keptPrefix_loopFree C pre hNo)
      (keptPrefix_sp C pre hNo) u).mpr ?_
  refine
    ⟨lift (flagExt_extensionOf Γ (normalize C).ids) s,
      ?_, ?_⟩
  · refine
      (retag_assert_eval_iff
        (flagExt_extensionOf Γ (normalize C).ids) pre hNo
        _).mpr ?_
    rw [project_lift]
    exact hPre
  · exact
      (bigStepEquiv_keptPrefix_of_no_push C pre hNo hP
        _ u).mpr hInit

/-
  The fixed-point hypothesis when nothing is pushed: every
  loop-head state satisfies the precondition and is a fixed
  point of the prefix.
-/
theorem loopHeadFixed_of_no_push
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols)
    (hP : (normalizedSplit C pre hNo).push = [])
    (u : Instance D (flagExt Γ (normalize C).ids))
    (hHead : (normalizedSplit C pre hNo).mid.eval u) :
    pre.eval
        (project (flagExt_extensionOf Γ (normalize C).ids)
          u) ∧
      Cmd.BigStep (normalize C).loop.init u u := by
  rcases
    loopHead_fixed (keptPrefix_loopFree C pre hNo)
      (keptPrefix_sp C pre hNo) hHead with
    ⟨hPreU, hFixed⟩
  refine ⟨?_, ?_⟩
  · exact
      (retag_assert_eval_iff
        (flagExt_extensionOf Γ (normalize C).ids) pre hNo
        u).mp hPreU
  · exact
      (bigStepEquiv_keptPrefix_of_no_push C pre hNo hP u
        u).mp hFixed

end Preprocess

end Whiel

------------------------------------------------------------
-- Transfer For The Preprocessor, After A Push
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/-
  The loop-head hypothesis after a push: the prefix runs the
  kept part and raises `p`, so the state entering the loop
  satisfies `φ_m` on its projection and has `p` up, which is
  exactly `pre' = φ_m ∧ p`.
-/
theorem loopHead_of_push
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols)
    {I : Cmd D (flagExt Γ (normalize C).ids)}
    {rest : List (Cmd D (flagExt Γ (normalize C).ids))}
    (s : Instance D Γ)
    (u :
      Instance D
        (flagExt Γ
          ((normalize C).ids ++ [normalizeNext C])))
    (hPre : pre.eval s)
    (hInit :
      Cmd.BigStep
        (pushFramed
          (flagExt_mono Γ (subsetAppendLeft _ _))
          (pushFlag C) (keptPrefix C pre hNo)
          (seqOfItems (I :: rest))
          (normalize C).loop).init
        (lift
          (flagExt_extensionOf Γ
            ((normalize C).ids ++ [normalizeNext C])) s)
        u) :
    (pushedPre (flagExt_mono Γ (subsetAppendLeft _ _))
        (pushFlag C) (normalizedSplit C pre hNo).mid
        (splitItems_mid_noBoundSymbols _
          (retagAssert_noBoundSymbols _ pre hNo))).eval
      u := by
  rcases
    flagInit_raise (flagExt_mono Γ (subsetAppendLeft _ _))
      (pushFlag_fresh C) hInit with ⟨hUp, hKeepRun⟩
  rw [pushedPre_eval_iff]
  refine ⟨?_, hUp⟩
  refine
    (loopHead_exact (keptPrefix_loopFree C pre hNo)
      (keptPrefix_sp C pre hNo) _).mpr ?_
  refine
    ⟨lift (flagExt_extensionOf Γ (normalize C).ids) s,
      ?_, ?_⟩
  · refine
      (retag_assert_eval_iff
        (flagExt_extensionOf Γ (normalize C).ids) pre hNo
        _).mpr ?_
    rw [project_lift]
    exact hPre
  · rw [← project_lift_trans
      (flagExt_extensionOf Γ (normalize C).ids)
      (flagExt_mono Γ (subsetAppendLeft _ _))
      (flagExt_extensionOf Γ
        ((normalize C).ids ++ [normalizeNext C])) s]
    exact hKeepRun

/-
  The fixed-point hypothesis after a push: `φ_m` makes the
  projection a fixed point of the kept part, and `p` is
  already up, so the whole pushed prefix returns.
-/
theorem loopHeadFixed_of_push
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols)
    {I : Cmd D (flagExt Γ (normalize C).ids)}
    {rest : List (Cmd D (flagExt Γ (normalize C).ids))}
    (u :
      Instance D
        (flagExt Γ
          ((normalize C).ids ++ [normalizeNext C])))
    (hHead :
      (pushedPre (flagExt_mono Γ (subsetAppendLeft _ _))
        (pushFlag C) (normalizedSplit C pre hNo).mid
        (splitItems_mid_noBoundSymbols _
          (retagAssert_noBoundSymbols _ pre hNo))).eval
        u) :
    pre.eval
        (project
          (flagExt_extensionOf Γ
            ((normalize C).ids ++ [normalizeNext C])) u) ∧
      Cmd.BigStep
        (pushFramed
          (flagExt_mono Γ (subsetAppendLeft _ _))
          (pushFlag C) (keptPrefix C pre hNo)
          (seqOfItems (I :: rest))
          (normalize C).loop).init u u := by
  rw [pushedPre_eval_iff] at hHead
  rcases hHead with ⟨hMid, hUp⟩
  rcases
    loopHead_fixed (keptPrefix_loopFree C pre hNo)
      (keptPrefix_sp C pre hNo) hMid with
    ⟨hPreU, hFixed⟩
  refine ⟨?_, ?_⟩
  · have hSplit :
        project
            (flagExt_extensionOf Γ
              ((normalize C).ids ++ [normalizeNext C]))
            u =
          project (flagExt_extensionOf Γ (normalize C).ids)
            (project
              (flagExt_mono Γ (subsetAppendLeft _ _))
              u) := by
      unfold project
      rw [Instance.reduct_trans]
    rw [hSplit]
    exact
      (retag_assert_eval_iff
        (flagExt_extensionOf Γ (normalize C).ids) pre hNo
        _).mp hPreU
  · exact
      Cmd.BigStep.seq
        (bigStep_retag_self_of_project_self _ hFixed)
        (bigStep_raise_self_of_up hUp)

end Preprocess

end Whiel

------------------------------------------------------------
-- Theorem "Transfer" And Corollary "Refutation Transfer"
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/- The suffix of the preprocessor's output is loop-free. -/
theorem preprocess_close_loopFree
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    (preprocess C pre hNo).loop.close.LoopFree :=
  cmdLoopFree_of_loopFree
    (preprocess_loopFreeParts C pre hNo).2.2

/-
  The loop-head assertion holds at every state the prefix
  reaches from a lifted start satisfying the precondition,
  in both cases of the split.
-/
theorem preprocess_loopHead
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    ∀ (s : Instance D Γ)
      (u :
        Instance D
          (flagExt Γ (preprocess C pre hNo).ids)),
      pre.eval s →
        Cmd.BigStep (preprocess C pre hNo).loop.init
            (lift
              (flagExt_extensionOf Γ
                (preprocess C pre hNo).ids) s)
            u →
          (preprocess C pre hNo).pre.eval u := by
  cases hP : (normalizedSplit C pre hNo).push with
  | nil =>
      rw [preprocess_eq_of_no_push C pre hNo hP]
      exact loopHead_of_no_push C pre hNo hP
  | cons I rest =>
      rw [preprocess_eq_of_push C pre hNo hP]
      exact loopHead_of_push C pre hNo

/-
  Lemma "Loop-head fixed point" for the preprocessor: every
  loop-head state satisfies the input precondition on its
  projection and is a fixed point of the post-split prefix.
-/
theorem preprocess_loopHead_fixed
    (C : Cmd D Γ)
    (pre : AssertExpr D Γ)
    (hNo : pre.NoBoundSymbols) :
    ∀ u :
        Instance D
          (flagExt Γ (preprocess C pre hNo).ids),
      (preprocess C pre hNo).pre.eval u →
        pre.eval
            (project
              (flagExt_extensionOf Γ
                (preprocess C pre hNo).ids) u) ∧
          Cmd.BigStep (preprocess C pre hNo).loop.init u
            u := by
  cases hP : (normalizedSplit C pre hNo).push with
  | nil =>
      rw [preprocess_eq_of_no_push C pre hNo hP]
      exact loopHeadFixed_of_no_push C pre hNo hP
  | cons I rest =>
      rw [preprocess_eq_of_push C pre hNo hP]
      exact loopHeadFixed_of_push C pre hNo

/-
  Theorem "Transfer": validity of the single-loop triple
  over the flag extension implies validity of the input
  triple for the packaged program.
-/
theorem preprocess_transfer_program
    (C : Cmd D Γ)
    (pre post : AssertExpr D Γ)
    (hNoPre : pre.NoBoundSymbols)
    (hNoPost : post.NoBoundSymbols)
    (hValid :
      HoareValid (preprocess C pre hNoPre).pre
        (.«while» (preprocess C pre hNoPre).loop.guard
          (preprocess C pre hNoPre).loop.body)
        (closingAssertion
          (flagExt_extensionOf Γ
            (preprocess C pre hNoPre).ids)
          (preprocess C pre hNoPre).loop
          (preprocess_close_loopFree C pre hNoPre) post
          hNoPost)) :
    Program.HoareValid pre
      (programOfFramed
        (flagExt_extensionOf Γ
          (preprocess C pre hNoPre).ids)
        (preprocess C pre hNoPre).loop)
      post :=
  transfer_of_loopHead _
    (preprocess_close_loopFree C pre hNoPre) hNoPost
    (preprocess_loopHead C pre hNoPre) hValid

/-
  Theorem "Transfer", concluded at the source command: the
  packaged program agrees with it, so validity carries the
  rest of the way to the input triple over `Γ`.
-/
theorem preprocess_transfer
    (C : Cmd D Γ)
    (pre post : AssertExpr D Γ)
    (hNoPre : pre.NoBoundSymbols)
    (hNoPost : post.NoBoundSymbols)
    (hValid :
      HoareValid (preprocess C pre hNoPre).pre
        (.«while» (preprocess C pre hNoPre).loop.guard
          (preprocess C pre hNoPre).loop.body)
        (closingAssertion
          (flagExt_extensionOf Γ
            (preprocess C pre hNoPre).ids)
          (preprocess C pre hNoPre).loop
          (preprocess_close_loopFree C pre hNoPre) post
          hNoPost)) :
    HoareValid pre.eval C post.eval :=
  hoareValid_of_transfer _
    (preprocess_equivMod C pre hNoPre)
    (preprocess_transfer_program C pre post hNoPre hNoPost
      hValid)

/-
  Corollary "Refutation transfer": a loop-head state from
  which the single loop terminates outside the closing
  assertion refutes the input triple, with witness its own
  projection --- which is the conclusion, so the witness the
  proof builds is returned rather than discarded.
-/
theorem preprocess_refutation
    (C : Cmd D Γ)
    (pre post : AssertExpr D Γ)
    (hNoPre : pre.NoBoundSymbols)
    (hNoPost : post.NoBoundSymbols)
    {u' v :
      Instance D (flagExt Γ (preprocess C pre hNoPre).ids)}
    (hHead : (preprocess C pre hNoPre).pre.eval u')
    (hLoop :
      Cmd.BigStep
        (.«while» (preprocess C pre hNoPre).loop.guard
          (preprocess C pre hNoPre).loop.body) u' v)
    (hFail :
      ¬ (closingAssertion
        (flagExt_extensionOf Γ
          (preprocess C pre hNoPre).ids)
        (preprocess C pre hNoPre).loop
        (preprocess_close_loopFree C pre hNoPre) post
        hNoPost).eval v) :
    pre.eval
        (project
          (flagExt_extensionOf Γ
            (preprocess C pre hNoPre).ids)
          u') ∧
      ∃ t : Instance D Γ,
        Cmd.BigStep C
            (project
              (flagExt_extensionOf Γ
                (preprocess C pre hNoPre).ids)
              u')
            t ∧
          ¬ post.eval t :=
  refutation_of_loopHead _
    (preprocess_close_loopFree C pre hNoPre) hNoPost
    (preprocess_equivMod C pre hNoPre)
    (preprocess_loopHead_fixed C pre hNoPre) hHead hLoop
    hFail

/-
  Corollary "Refutation transfer" for the preprocessor, read
  as the invalidity of the input triple.
-/
theorem preprocess_not_hoareValid
    (C : Cmd D Γ)
    (pre post : AssertExpr D Γ)
    (hNoPre : pre.NoBoundSymbols)
    (hNoPost : post.NoBoundSymbols)
    {u' v :
      Instance D (flagExt Γ (preprocess C pre hNoPre).ids)}
    (hHead : (preprocess C pre hNoPre).pre.eval u')
    (hLoop :
      Cmd.BigStep
        (.«while» (preprocess C pre hNoPre).loop.guard
          (preprocess C pre hNoPre).loop.body) u' v)
    (hFail :
      ¬ (closingAssertion
        (flagExt_extensionOf Γ
          (preprocess C pre hNoPre).ids)
        (preprocess C pre hNoPre).loop
        (preprocess_close_loopFree C pre hNoPre) post
        hNoPost).eval v) :
    ¬ HoareValid pre.eval C post.eval :=
  not_hoareValid_of_loopHead _
    (preprocess_close_loopFree C pre hNoPre) hNoPost
    (preprocess_equivMod C pre hNoPre)
    (preprocess_loopHead_fixed C pre hNoPre) hHead hLoop
    hFail

end Preprocess

end Whiel
