-- Author: Jesse Comer
import Whiel.Cmd.ConcurrentProduct
import Whiel.DatalogCompiler.Naive

/-
  This file packages the generic concurrent-product theory
  for output of the completed naive Datalog compiler.

  Key definitions include:
    * `Datalog.WhielCompiler.Naive.concurrentInvariant`
    * `Datalog.WhielCompiler.Naive.concurrentInitCmd`

  The main construction is:
    * `Datalog.WhielCompiler.Naive.concurrentComponent`

  Correctness is proven by the initialization, maintenance,
  and stutter theorems used by `concurrentComponent`.

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Generated Execution-State Views
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Every generated snapshot name belongs to an IDB. -/
theorem snapshotRawOf_surjective
    (P : Datalog.Program D Γ)
    {Y : A}
    (hY : Y ∈ snapshotNames P) :
    ∃ X : IDBSym P, snapshotRawOf P X = Y := by
  let i := (snapshotNames P).idxOf Y
  have hiSnap : i < (snapshotNames P).length :=
    List.idxOf_lt_length_of_mem hY
  have hiIdb : i < (idbList P).length := by
    rw [← snapshotNames_length P]
    exact hiSnap
  let X0 : Γ.syms :=
    (idbList P)[i]'hiIdb
  have hX0 : X0 ∈ idbList P :=
    List.getElem_mem hiIdb
  let X : IDBSym P :=
    ⟨X0, idbList_mem_idb P hX0⟩
  refine ⟨X, ?_⟩
  have hNodup : (idbList P).Nodup := by
    unfold idbList Program.idbList
    let rec hAll (L : List Γ.syms) :
        L.eraseDups.Nodup := by
      cases L with
      | nil => simp
      | cons Z Zs =>
        rw [List.eraseDups_cons]
        apply List.Nodup.cons
        · intro hMem
          have hOrig : Z ∈ List.filter
              (fun W => !W == Z) Zs :=
            List.mem_eraseDups.mp hMem
          simp at hOrig
        · exact hAll (List.filter
            (fun W => !W == Z) Zs)
      termination_by L.length
      decreasing_by
        exact lt_of_le_of_lt
          (List.length_filter_le _ _)
          (Nat.lt_succ_self _)
    exact hAll P.headSymbolList
  have hIndex : idbIndex P X = i := by
    have hAtIndex :
        (idbList P)[idbIndex P X]'(idbIndex_lt P X) =
          (idbList P)[i]'hiIdb := by
      rw [idbList_get_idbIndex P X]
    exact hNodup.getElem_inj_iff.mp hAtIndex
  unfold snapshotRawOf
  simp only [hIndex]
  exact List.getElem_idxOf hiSnap

/- Live and snapshot views determine an execution state. -/
theorem eq_of_liveState_eq_snapshotState_eq
    (P : Datalog.Program D Γ)
    {J K : Instance D (execSchema P)}
    (hLive : liveState P J = liveState P K)
    (hSnapshot :
      snapshotState P J = snapshotState P K) :
    J = K := by
  apply Instance.ext
  intro X
  rcases Finset.mem_union.mp X.2 with
    hProg | hSnapshotName
  · let hExt := execSchema_extension_output P
    have hJ :
        Instance.Extends hExt (liveState P J) J := by
      apply Instance.extends_of_reduct_eq hExt
      rfl
    have hK :
        Instance.Extends hExt (liveState P J) K := by
      apply Instance.extends_of_reduct_eq hExt
      exact hLive.symm
    exact (hJ X hProg).trans (hK X hProg).symm
  · have hList : X.1 ∈ snapshotNames P := by
      simpa using hSnapshotName
    rcases snapshotRawOf_surjective P hList with
      ⟨Y, hY⟩
    have hX : X = snapshotOf P Y := by
      exact Subtype.ext hY.symm
    subst hX
    have hRel :
        snapshotIDBRel P J Y =
          snapshotIDBRel P K Y := by
      rw [← snapshotState_idb P J Y]
      rw [← snapshotState_idb P K Y]
      exact congrFun hSnapshot Y.1
    unfold snapshotIDBRel at hRel
    exact
      (Equiv.cast
        (congrArg (FinRelation D)
          (snapshotOf_arity P Y))).injective hRel

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Naive Loop Invariant
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The compiler state is one immediate step ahead. -/
def concurrentInvariant
    (P : Datalog.Program D Γ)
    (J : Instance D (execSchema P)) : Prop :=
  liveState P J =
    P.immediate (snapshotState P J)

/- Initialization before the generated while command. -/
def concurrentInitCmd
    (P : Datalog.Program D Γ) :
    Whiel.Cmd D (execSchema P) :=
  seqList
    (((idbSymList P).map
      (emptySnapshotIDBCmd P)) ++
      ((idbSymList P).map
        (initialStepIDBCmd P)))

/- Compiler initialization establishes the invariant. -/
theorem concurrentInitCmd_establishes_invariant
    (P : Datalog.Program D Γ)
    (I : Instance D P.edbSchema)
    {J : Instance D (execSchema P)}
    (hStep : Whiel.Cmd.BigStep
      (concurrentInitCmd P)
      ((P.toWhielProgram).initialInstance I) J) :
    concurrentInvariant P J := by
  let Jempty :=
    emptySnapshotsState P
      ((P.toWhielProgram).initialInstance I)
      (idbSymList P)
  let Jinit :=
    initialStepIDBsState P Jempty (idbSymList P)
  have hEmpty :
      Whiel.Cmd.BigStep (emptySnapshotsCmd P)
        ((P.toWhielProgram).initialInstance I)
        Jempty :=
    emptySnapshotsCmd_bigStep_state P _
  have hInitial :
      Whiel.Cmd.BigStep (initialStepCmd P)
        Jempty Jinit :=
    initialStepCmd_bigStep_state P _
  have hCanonical :
      Whiel.Cmd.BigStep (concurrentInitCmd P)
        ((P.toWhielProgram).initialInstance I)
        Jinit :=
    Datalog.WhielCompiler.seqList_append_bigStep
      hEmpty hInitial
  have hJ : J = Jinit :=
    hStep.deterministic hCanonical
  subst hJ
  unfold concurrentInvariant
  have hEmptySnapshot :
      snapshotState P Jempty = P.initial I := by
    dsimp [Jempty]
    exact
      snapshotState_emptySnapshotsState_initial P I
  have hEmptyLive :
      liveState P Jempty = P.initial I := by
    dsimp [Jempty]
    exact liveState_emptySnapshotsState_initial P I
  have hFinalSnapshot :
      snapshotState P Jinit = P.initial I := by
    dsimp [Jinit]
    rw [snapshotState_initialStepIDBsState]
    exact hEmptySnapshot
  have hFinalLive :
      liveState P Jinit =
        P.immediate (P.initial I) := by
    dsimp [Jinit]
    exact
      liveState_initialStepIDBsState_immediate_initial
        P I Jempty hEmptySnapshot hEmptyLive
  rw [hFinalSnapshot]
  exact hFinalLive

/- Every generated iteration reestablishes the invariant. -/
theorem iterationCmd_preserves_concurrentInvariant
    (P : Datalog.Program D Γ)
    {J K : Instance D (execSchema P)}
    (_hInv : concurrentInvariant P J)
    (hStep : Whiel.Cmd.BigStep
      (iterationCmd P) J K) :
    concurrentInvariant P K := by
  let Jnext :=
    stepIDBsState P
      (snapshotIDBsState P J (idbSymList P))
      (idbSymList P)
  have hCanonical :
      Whiel.Cmd.BigStep (iterationCmd P) J Jnext :=
    iterationCmd_bigStep_state P J
  have hK : K = Jnext :=
    hStep.deterministic hCanonical
  subst hK
  unfold concurrentInvariant
  have hSnapshot :
      snapshotState P Jnext = liveState P J := by
    dsimp [Jnext]
    calc
      snapshotState P
          (stepIDBsState P
            (snapshotIDBsState P J (idbSymList P))
            (idbSymList P)) =
        snapshotState P
          (snapshotIDBsState P J (idbSymList P)) :=
        snapshotState_stepIDBsState P _ _
      _ = liveState P J :=
        snapshotState_snapshotIDBsState_eq_liveState
          P J
  rw [hSnapshot]
  exact liveState_iterationState_immediate P J

/- At a false guard, the unmodified body is a stutter. -/
theorem iterationCmd_stutters_when_done
    (P : Datalog.Program D Γ)
    {J : Instance D (execSchema P)}
    (hInv : concurrentInvariant P J)
    (hDone :
      ¬ Whiel.Guard.eval (changedGuard P) J) :
    Whiel.Cmd.BigStep (iterationCmd P) J J := by
  have hViews :
      liveState P J = snapshotState P J := by
    by_contra hNe
    exact hDone
      ((changedGuard_eval_iff_liveState_ne_snapshotState
        P J).mpr hNe)
  let Jnext :=
    stepIDBsState P
      (snapshotIDBsState P J (idbSymList P))
      (idbSymList P)
  have hStep :
      Whiel.Cmd.BigStep (iterationCmd P) J Jnext :=
    iterationCmd_bigStep_state P J
  have hSnapshot :
      snapshotState P Jnext = snapshotState P J := by
    dsimp [Jnext]
    calc
      snapshotState P
          (stepIDBsState P
            (snapshotIDBsState P J (idbSymList P))
            (idbSymList P)) =
        snapshotState P
          (snapshotIDBsState P J (idbSymList P)) :=
        snapshotState_stepIDBsState P _ _
      _ = liveState P J :=
        snapshotState_snapshotIDBsState_eq_liveState
          P J
      _ = snapshotState P J := hViews
  have hLive : liveState P Jnext = liveState P J := by
    dsimp [Jnext]
    calc
      liveState P
          (stepIDBsState P
            (snapshotIDBsState P J (idbSymList P))
            (idbSymList P)) =
        P.immediate (liveState P J) :=
          liveState_iterationState_immediate P J
      _ = P.immediate (snapshotState P J) := by
        rw [hViews]
      _ = liveState P J := hInv.symm
  have hEq : Jnext = J :=
    eq_of_liveState_eq_snapshotState_eq
      P hLive hSnapshot
  simpa [hEq] using hStep

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Compiled Command Framing
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Both command-list implementations are definitionally
  pointwise equal. -/
theorem compilerSeqList_eq_cmdSeqList
    (Cs : List (Whiel.Cmd D Γ)) :
    Datalog.WhielCompiler.seqList Cs =
      Whiel.Cmd.seqList Cs := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih =>
      simp [Datalog.WhielCompiler.seqList,
        Whiel.Cmd.seqList, ih]

/- The cleaned compiler output has the certified frame. -/
theorem toWhielCmd_concurrent_framed_equiv
    (P : Datalog.Program D Γ) :
    Whiel.Cmd.BigStepEquiv P.toWhielCmd
      (Whiel.Cmd.framedLoopCommand
        (concurrentInitCmd P)
        (changedGuard P)
        (iterationCmd P)
        .skip) := by
  intro I J
  rw [Datalog.Program.toWhielCmd]
  rw [Whiel.Cmd.bigStep_clean_iff]
  unfold cmdCore concurrentInitCmd
  let initList :=
    ((idbSymList P).map
      (emptySnapshotIDBCmd P)) ++
      ((idbSymList P).map
        (initialStepIDBCmd P))
  change
    Whiel.Cmd.BigStep
        (Datalog.WhielCompiler.seqList
          (initList ++
            [Whiel.Cmd.«while» (changedGuard P)
              (iterationCmd P)])) I J ↔ _
  rw [compilerSeqList_eq_cmdSeqList]
  rw [Whiel.Cmd.bigStep_seqList_framedLoopParts_iff
    initList (changedGuard P) (iterationCmd P) [] I J]
  simp only [Whiel.Cmd.seqList]
  rw [← compilerSeqList_eq_cmdSeqList]

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Component Construction Support
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Guards only mention names in their schema. -/
theorem guard_symbols_subset_schema
    (G : Whiel.Guard D Γ) :
    G.symbols ⊆ Γ.syms := by
  induction G with
  | «true» => simp [Whiel.Guard.symbols]
  | «false» => simp [Whiel.Guard.symbols]
  | eq e₁ e₂ =>
      simpa [Whiel.Guard.symbols] using
        Finset.union_subset e₁.symbols_subset
          e₂.symbols_subset
  | subset e₁ e₂ =>
      simpa [Whiel.Guard.symbols] using
        Finset.union_subset e₁.symbols_subset
          e₂.symbols_subset
  | and G H ihG ihH =>
      simpa [Whiel.Guard.symbols] using
        Finset.union_subset ihG ihH
  | or G H ihG ihH =>
      simpa [Whiel.Guard.symbols] using
        Finset.union_subset ihG ihH
  | not G ih =>
      simpa [Whiel.Guard.symbols] using ih

/- Commands only mention names in their schema. -/
theorem cmd_symbols_subset_schema
    (C : Whiel.Cmd D Γ) :
    C.symbols ⊆ Γ.syms := by
  induction C with
  | «skip» => simp [Whiel.Cmd.symbols]
  | assign X e =>
      simpa [Whiel.Cmd.symbols] using
        Finset.union_subset
          (Finset.singleton_subset_iff.mpr X.2)
          e.symbols_subset
  | seq C₁ C₂ ih₁ ih₂ =>
      simpa [Whiel.Cmd.symbols] using
        Finset.union_subset ih₁ ih₂
  | ite G C₁ C₂ ih₁ ih₂ =>
      simpa [Whiel.Cmd.symbols] using
        Finset.union_subset
          (guard_symbols_subset_schema G)
          (Finset.union_subset ih₁ ih₂)
  | «while» G C ih =>
      simpa [Whiel.Cmd.symbols] using
        Finset.union_subset
          (guard_symbols_subset_schema G) ih

/- Generated initialization contains no while command. -/
theorem concurrentInitCmd_loopFree
    (P : Datalog.Program D Γ) :
    (concurrentInitCmd P).LoopFree := by
  unfold concurrentInitCmd
  rw [compilerSeqList_eq_cmdSeqList]
  rw [Whiel.Cmd.loopFree_seqList_iff]
  intro C hC
  simp only [List.mem_append, List.mem_map] at hC
  rcases hC with
    ⟨X, _hX, rfl⟩ | ⟨X, _hX, rfl⟩
  · simp [emptySnapshotIDBCmd, Whiel.Cmd.LoopFree]
  · simp [initialStepIDBCmd, Whiel.Cmd.LoopFree]

/- Generated iterations contain no while command. -/
theorem iterationCmd_loopFree
    (P : Datalog.Program D Γ) :
    (iterationCmd P).LoopFree := by
  unfold iterationCmd
  rw [compilerSeqList_eq_cmdSeqList]
  rw [Whiel.Cmd.loopFree_seqList_iff]
  intro C hC
  simp only [List.mem_append, List.mem_map] at hC
  rcases hC with
    ⟨X, _hX, rfl⟩ | ⟨X, _hX, rfl⟩
  · simp [snapshotIDBCmd, Whiel.Cmd.LoopFree]
  · simp [stepIDBCmd, Whiel.Cmd.LoopFree]

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
-- Generic Compiled Component
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

namespace Naive

variable {A D : Type}
variable [Whiel.RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Every completed naive compiler output is a certified
  concurrent-product component. -/
def concurrentComponent
    (P : Datalog.Program D Γ) :
    Whiel.ConcurrentProduct.Component
      (A := A) (D := D) where
  inputSchema := P.edbSchema
  outputSchema := Γ
  program := P.toWhielProgram
  init := concurrentInitCmd P
  guard := changedGuard P
  body := iterationCmd P
  close := .skip
  footprint := (execSchema P).syms
  footprint_subset := by
    intro X hX
    exact hX
  input_subset := (execSchema_extension_input P).1
  output_subset := (execSchema_extension_output P).1
  init_symbols := cmd_symbols_subset_schema _
  guard_symbols := guard_symbols_subset_schema _
  body_symbols := cmd_symbols_subset_schema _
  close_symbols := by simp [Whiel.Cmd.symbols]
  init_loopFree := concurrentInitCmd_loopFree P
  body_loopFree := iterationCmd_loopFree P
  close_loopFree := Whiel.Cmd.loopFree_skip
  invariant := concurrentInvariant P
  invariant_local := by
    intro I J hAgree
    have hEq : I = J := by
      apply Instance.ext
      intro X
      exact hAgree X X.2
    subst hEq
    rfl
  init_invariant :=
    concurrentInitCmd_establishes_invariant P
  body_invariant :=
    iterationCmd_preserves_concurrentInvariant P
  body_stutter :=
    iterationCmd_stutters_when_done P
  cmd_equiv :=
    toWhielCmd_concurrent_framed_equiv P

end Naive

end WhielCompiler

end Datalog

------------------------------------------------------------
