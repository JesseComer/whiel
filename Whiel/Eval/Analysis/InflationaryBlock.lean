-- Author: Jesse Comer
import Whiel.Cmd.ConcurrentProduct
import Databases.UnnamedRA.SPJU.Syntax

/-
  This file recognizes and certifies synchronous
  inflationary command blocks.

  Key definitions include:
    * `Whiel.InflationaryBlock.Block`
    * `Whiel.InflationaryBlock.PositiveBlock`
    * `Whiel.InflationaryBlock.recognize`

  Correctness is expressed by the block execution, growth,
  locality, invariant-preservation, and stutter theorems.
-/

------------------------------------------------------------
-- Block Entries
------------------------------------------------------------

namespace Whiel

namespace InflationaryBlock

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- One snapshot/live accumulator pair and its derivation. -/
structure Entry (D : Type) [Domain D]
    (Γ : UnnamedSchema A) where
  snapshot : Γ.syms
  live : Γ.syms
  arity_eq : Γ.arity snapshot = Γ.arity live
  derive : RAExpr D Γ (Γ.arity live)

namespace Entry

/- The snapshot assignment for one entry. -/
def snapshotCmd (E : Entry D Γ) : Cmd D Γ :=
  .assign E.snapshot
    (RAExpr.relAs E.snapshot E.live E.arity_eq)

/- The inflationary live assignment for one entry. -/
def updateCmd (E : Entry D Γ) : Cmd D Γ :=
  .assign E.live
    (RAExpr.union (RAExpr.rel E.live) E.derive)

/- The equality atom used by the local guard. -/
def equalGuard (E : Entry D Γ) : Guard D Γ :=
  .eq (RAExpr.rel E.live)
    (RAExpr.relAs E.live E.snapshot E.arity_eq.symm)

/- Symbols read by the derivation. -/
def dependencies (E : Entry D Γ) : Finset A :=
  E.derive.symbols

end Entry

end InflationaryBlock

end Whiel

------------------------------------------------------------
-- Canonical Block Syntax
------------------------------------------------------------

namespace Whiel

namespace InflationaryBlock

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Conjunction with `true` as its list identity. -/
def andList : List (Guard D Γ) → Guard D Γ
| [] => .«true»
| G :: Gs => .and G (andList Gs)

/- Flatten conjunctions and erase `true` identities. -/
def flattenAnd : Guard D Γ → List (Guard D Γ)
| .and G H => flattenAnd G ++ flattenAnd H
| .«true» => []
| G => [G]

/- All snapshots, followed by all live updates. -/
def canonicalBody (Es : List (Entry D Γ)) : Cmd D Γ :=
  Cmd.seqList
    (Es.map Entry.snapshotCmd ++ Es.map Entry.updateCmd)

/- The local continuation guard. -/
def canonicalGuard (Es : List (Entry D Γ)) : Guard D Γ :=
  .not (andList (Es.map Entry.equalGuard))

@[simp] theorem andList_eval_iff
    (Gs : List (Guard D Γ))
    (I : Instance D Γ) :
    (andList Gs).eval I ↔ ∀ G ∈ Gs, G.eval I := by
  induction Gs with
  | nil => simp [andList]
  | cons G Gs ih => simp [andList, ih]

/- Flattening conjunctions preserves guard evaluation. -/
theorem flattenAnd_eval_iff
    (G : Guard D Γ)
    (I : Instance D Γ) :
    (andList (flattenAnd G)).eval I ↔ G.eval I := by
  induction G with
  | «true» => simp [flattenAnd, andList]
  | «false» => simp [flattenAnd, andList]
  | eq e₁ e₂ => simp [flattenAnd, andList]
  | subset e₁ e₂ => simp [flattenAnd, andList]
  | and G H ihG ihH =>
      rw [andList_eval_iff]
      constructor
      · intro h
        constructor
        · apply ihG.mp
          apply (andList_eval_iff _ _).mpr
          intro K hK
          exact h K (by simp [flattenAnd, hK])
        · apply ihH.mp
          apply (andList_eval_iff _ _).mpr
          intro K hK
          exact h K (by simp [flattenAnd, hK])
      · rintro ⟨hG, hH⟩ K hK
        simp only [flattenAnd, List.mem_append] at hK
        rcases hK with hK | hK
        · exact (andList_eval_iff _ _).mp
            (ihG.mpr hG) K hK
        · exact (andList_eval_iff _ _).mp
            (ihH.mpr hH) K hK
  | or G H ihG ihH => simp [flattenAnd, andList]
  | not G ih => simp [flattenAnd, andList]

end InflationaryBlock

end Whiel

------------------------------------------------------------
-- Proof-Carrying Blocks
------------------------------------------------------------

namespace Whiel

namespace InflationaryBlock

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A checked nonempty inflationary block. -/
structure Block
    (G : Guard D Γ) (C : Cmd D Γ) where
  entries : List (Entry D Γ)
  nonempty : entries ≠ []
  live_nodup : (entries.map fun E => E.live.1).Nodup
  snapshot_nodup :
    (entries.map fun E => E.snapshot.1).Nodup
  targets_disjoint :
    ∀ E ∈ entries, ∀ F ∈ entries,
      E.snapshot.1 ≠ F.live.1
  body_equiv : Cmd.BigStepEquiv C (canonicalBody entries)
  guard_equiv :
    ∀ I : Instance D Γ,
      G.eval I ↔ (canonicalGuard entries).eval I

/- Positive refinement using the existing SPJU property. -/
structure PositiveBlock
    (G : Guard D Γ) (C : Cmd D Γ) extends Block G C where
  positive : ∀ E ∈ entries, E.derive.IsSPJU

namespace Block

private def targets : List (Entry D Γ) → Finset A
| [] => ∅
| E :: Es =>
    insert E.snapshot.1 (insert E.live.1 (targets Es))

private def allSymbols : List (Entry D Γ) → Finset A
| [] => ∅
| E :: Es =>
    insert E.snapshot.1
      (insert E.live.1 (E.dependencies ∪ allSymbols Es))

/- All snapshot and live write targets. -/
def writeTargets
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) : Finset A :=
  targets B.entries

/- Targets and all recorded derivation dependencies. -/
def footprint
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) : Finset A :=
  allSymbols B.entries

end Block

end InflationaryBlock

end Whiel

------------------------------------------------------------
-- Executable Recognition Support
------------------------------------------------------------

namespace Whiel

namespace InflationaryBlock

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem raExpr_eq_of_expr_eq
    {n : Nat} {e f : RAExpr D Γ n}
    (h : e.expr = f.expr) : e = f := by
  cases e
  cases f
  cases h
  rfl

private theorem union_wf
    (e₁ e₂ : RawRAExpr A D)
    (hAr :
      (RawRAExpr.union e₁ e₂).arity? Γ = some n) :
    e₁.arity? Γ = some n ∧
      e₂.arity? Γ = some n := by
  cases h₁ : e₁.arity? Γ with
  | none => simp [RawRAExpr.arity?, h₁] at hAr
  | some n₁ =>
      cases h₂ : e₂.arity? Γ with
      | none => simp [RawRAExpr.arity?, h₁, h₂] at hAr
      | some n₂ =>
          by_cases hEq : n₁ = n₂
          · subst n₂
            have hn : n₁ = n := by
              simpa [RawRAExpr.arity?, h₁, h₂] using hAr
            exact ⟨congrArg some hn, congrArg some hn⟩
          · simp [RawRAExpr.arity?, h₁, h₂, hEq] at hAr

private structure Snapshot where
  snapshot : Γ.syms
  live : Γ.syms
  arity_eq : Γ.arity snapshot = Γ.arity live

namespace Snapshot

private def entry (S : Snapshot (Γ := Γ))
    (derive : RAExpr D Γ (Γ.arity S.live)) : Entry D Γ :=
  ⟨S.snapshot, S.live, S.arity_eq, derive⟩

private def command (S : Snapshot (Γ := Γ)) : Cmd D Γ :=
  .assign S.snapshot
    (RAExpr.relAs S.snapshot S.live S.arity_eq)

end Snapshot

private structure Update where
  live : Γ.syms
  derive : RAExpr D Γ (Γ.arity live)

namespace Update

private def command
    (U : Update (D := D) (Γ := Γ)) : Cmd D Γ :=
  .assign U.live
    (RAExpr.union (RAExpr.rel U.live) U.derive)

end Update

private def snapshot?
    (C : Cmd D Γ) :
    Option {S : Snapshot (Γ := Γ) // S.command = C} :=
  match C with
  | .assign X e =>
      match hExpr : e.expr with
      | .rel Y =>
          if hY : Y ∈ Γ.syms then
            let live : Γ.syms := ⟨Y, hY⟩
            let hAr : Γ.arity X = Γ.arity live := by
              have hWf := e.wf
              rw [hExpr] at hWf
              symm
              simpa [RawRAExpr.arity?,
                UnnamedSchema.arity?, hY] using hWf
            let S : Snapshot (Γ := Γ) :=
              ⟨X, live, hAr⟩
            some ⟨S, by
              apply congrArg (Cmd.assign X)
              apply raExpr_eq_of_expr_eq
              simpa [S, Snapshot.command, RAExpr.relAs,
                RAExpr.castArity, RAExpr.rel]
                using hExpr.symm⟩
          else none
      | _ => none
  | _ => none

private def update?
    (C : Cmd D Γ) :
    Option {U : Update (D := D) (Γ := Γ) //
      U.command = C} :=
  match C with
  | .assign X e =>
      match hExpr : e.expr with
      | .union (.rel Y) raw =>
          if hYX : Y = X.1 then
            let hChildren := union_wf (.rel Y) raw
              (by simpa [hExpr] using e.wf)
            let derive : RAExpr D Γ (Γ.arity X) :=
              ⟨raw, hChildren.2⟩
            let U : Update (D := D) (Γ := Γ) :=
              ⟨X, derive⟩
            some ⟨U, by
              apply congrArg (Cmd.assign X)
              apply raExpr_eq_of_expr_eq
              simpa [U, Update.command, RAExpr.union,
                RAExpr.rel, hYX] using hExpr.symm⟩
          else none
      | _ => none
  | _ => none

private def parseSnapshots :
    (Cs : List (Cmd D Γ)) →
      Option {Ss : List (Snapshot (Γ := Γ)) //
        Ss.map Snapshot.command = Cs}
| [] => some ⟨[], rfl⟩
| C :: Cs =>
    match snapshot? C, parseSnapshots Cs with
    | some ⟨S, hS⟩, some ⟨Ss, hSs⟩ =>
        some ⟨S :: Ss, by simp [hS, hSs]⟩
    | _, _ => none

private def parseUpdates :
    (Cs : List (Cmd D Γ)) →
      Option {Us : List (Update (D := D) (Γ := Γ)) //
        Us.map Update.command = Cs}
| [] => some ⟨[], rfl⟩
| C :: Cs =>
    match update? C, parseUpdates Cs with
    | some ⟨U, hU⟩, some ⟨Us, hUs⟩ =>
        some ⟨U :: Us, by simp [hU, hUs]⟩
    | _, _ => none

private def combine :
    (Ss : List (Snapshot (Γ := Γ))) →
    (Us : List (Update (D := D) (Γ := Γ))) →
    Option {Es : List (Entry D Γ) //
      Es.map Entry.snapshotCmd = Ss.map Snapshot.command ∧
      Es.map Entry.updateCmd = Us.map Update.command}
| [], [] => some ⟨[], rfl, rfl⟩
| S :: Ss, U :: Us =>
    if hLive : S.live = U.live then
      match combine Ss Us with
      | some ⟨Es, hSnap, hUpdate⟩ =>
          let hAr : Γ.arity S.snapshot =
              Γ.arity U.live :=
            S.arity_eq.trans (congrArg Γ.arity hLive)
          let E : Entry D Γ :=
            ⟨S.snapshot, U.live, hAr, U.derive⟩
          some ⟨E :: Es, by
            constructor
            · apply congrArg₂ List.cons
              · unfold Entry.snapshotCmd Snapshot.command
                apply congrArg (Cmd.assign S.snapshot)
                apply raExpr_eq_of_expr_eq
                simp [RAExpr.relAs, RAExpr.castArity,
                  RAExpr.rel, E, hLive]
              · exact hSnap
            · apply congrArg₂ List.cons
              · rfl
              · exact hUpdate⟩
      | none => none
    else none
| _, _ => none

private structure AtomEvidence
    (E : Entry D Γ) (G : Guard D Γ) where
  token : Unit
  sound : ∀ I : Instance D Γ,
    G.eval I ↔ E.equalGuard.eval I

private def equalAtom?
    (E : Entry D Γ) (G : Guard D Γ) :
    Option (AtomEvidence E G) :=
  match G with
  | .eq (n := n) e₁ e₂ =>
      if h₁ : e₁.expr = .rel E.live.1 then
        if h₂ : e₂.expr = .rel E.snapshot.1 then
          some ⟨(), by
            intro I
            have hn : n = Γ.arity E.live := by
              have hWf := e₁.wf
              rw [h₁] at hWf
              simpa [RawRAExpr.arity?,
                UnnamedSchema.arity?, E.live.2]
                using hWf.symm
            subst n
            have he₁ : e₁ = RAExpr.rel E.live :=
              raExpr_eq_of_expr_eq h₁
            have he₂ :
                e₂ = RAExpr.relAs E.live E.snapshot
                  E.arity_eq.symm := by
              apply raExpr_eq_of_expr_eq
              simpa [RAExpr.relAs, RAExpr.castArity,
                RAExpr.rel] using h₂
            simp [Entry.equalGuard, he₁, he₂]⟩
        else none
      else none
  | _ => none

private structure GuardEvidence
    (Es : List (Entry D Γ))
    (Gs : List (Guard D Γ)) where
  token : Unit
  sound : ∀ I : Instance D Γ,
    (andList Gs).eval I ↔
      (andList (Es.map Entry.equalGuard)).eval I

private def guardAtoms? :
    (Es : List (Entry D Γ)) →
    (Gs : List (Guard D Γ)) →
    Option (GuardEvidence Es Gs)
| [], [] => some ⟨(), by intro I; rfl⟩
| E :: Es, G :: Gs =>
    match equalAtom? E G, guardAtoms? Es Gs with
    | some hHead, some hTail =>
        some ⟨(), by
          intro I
          simp only [andList, Guard.eval_and_iff]
          exact and_congr (hHead.sound I) (hTail.sound I)⟩
    | _, _ => none
| _, _ => none

private theorem take_append_drop
    (k : Nat) (xs : List α) :
    xs.take k ++ xs.drop k = xs := by
  exact List.take_append_drop k xs

private def snapshotCommands
    (Es : List (Entry D Γ)) : List (Cmd D Γ) :=
  Es.map Entry.snapshotCmd

private def updateCommands
    (Es : List (Entry D Γ)) : List (Cmd D Γ) :=
  Es.map Entry.updateCmd

private theorem body_equiv_of_list_eq
    (C : Cmd D Γ) (Es : List (Entry D Γ))
    (hLists :
      snapshotCommands Es ++
        updateCommands Es = C.flattenSeq) :
    Cmd.BigStepEquiv C (canonicalBody Es) := by
  intro I J
  unfold snapshotCommands updateCommands at hLists
  rw [canonicalBody, hLists]
  exact (Cmd.bigStep_seqList_flattenSeq_iff C I J).symm

/- Recognize the checked body and guard shapes. -/
def recognize
    (G : Guard D Γ) (C : Cmd D Γ) :
    Option (Block G C) :=
  let Cs := C.flattenSeq
  let k := Cs.length / 2
  if hNonzero : k ≠ 0 then
    if hLength : k + k = Cs.length then
      match parseSnapshots (Cs.take k),
          parseUpdates (Cs.drop k) with
      | some ⟨Ss, hSs⟩, some ⟨Us, hUs⟩ =>
          match combine Ss Us with
          | some ⟨Es, hSnap, hUpdate⟩ =>
              if hEs : Es ≠ [] then
                if hLive :
                    (Es.map fun E => E.live.1).Nodup then
                  if hSnapshot :
                    (Es.map fun E =>
                      E.snapshot.1).Nodup then
                    if hDisjoint :
                        ∀ E ∈ Es, ∀ F ∈ Es,
                          E.snapshot.1 ≠ F.live.1 then
                      match G with
                      | .not H =>
                          match guardAtoms? Es
                              (flattenAnd H) with
                          | some hGuard =>
                              some {
                                entries := Es
                                nonempty := hEs
                                live_nodup := hLive
                                snapshot_nodup := hSnapshot
                                targets_disjoint :=
                                  hDisjoint
                                body_equiv := by
                                  have hLists :
                                      snapshotCommands Es ++
                                      updateCommands Es =
                                        Cs := by
                                    unfold snapshotCommands
                                      updateCommands
                                    rw [hSnap, hUpdate,
                                      hSs, hUs]
                                    exact
                                      take_append_drop k Cs
                                  exact
                                    body_equiv_of_list_eq
                                      C Es hLists
                                guard_equiv := by
                                  intro I
                                  change (¬ H.eval I) ↔ _
                                  rw [←
                                    flattenAnd_eval_iff H I]
                                  exact not_congr
                                    (hGuard.sound I) }
                          | none => none
                      | _ => none
                    else none
                  else none
                else none
              else none
          | none => none
      | _, _ => none
    else none
  else none

/- Recognize the SPJU-positive refinement. -/
def recognizePositive
    (G : Guard D Γ) (C : Cmd D Γ) :
    Option (PositiveBlock G C) :=
  match recognize G C with
  | some B =>
      if hPositive :
          ∀ E ∈ B.entries, E.derive.IsSPJU then
        some { toBlock := B, positive := hPositive }
      else none
  | none => none

/- Successful base recognition returns sound evidence. -/
theorem recognize_sound
    {G : Guard D Γ} {C : Cmd D Γ}
    {B : Block G C}
    (_h : recognize G C = some B) :
    Cmd.BigStepEquiv C (canonicalBody B.entries) ∧
      (∀ I, G.eval I ↔
        (canonicalGuard B.entries).eval I) := by
  exact ⟨B.body_equiv, B.guard_equiv⟩

/- Positive recognition certifies every derivation. -/
theorem recognizePositive_sound
    {G : Guard D Γ} {C : Cmd D Γ}
    {B : PositiveBlock G C}
    (_h : recognizePositive G C = some B) :
    ∀ E ∈ B.entries, E.derive.IsSPJU := by
  exact B.positive

end InflationaryBlock

end Whiel

------------------------------------------------------------
-- Explicit Block Execution
------------------------------------------------------------

namespace Whiel

namespace InflationaryBlock

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Execute all snapshot assignments. -/
def snapshotState :
    List (Entry D Γ) → Instance D Γ → Instance D Γ
| [], I => I
| E :: Es, I =>
    snapshotState Es
      (Instance.update I E.snapshot
        ((RAExpr.relAs E.snapshot E.live
          E.arity_eq).eval I))

/- Execute all inflationary live updates. -/
def updateState :
    List (Entry D Γ) → Instance D Γ → Instance D Γ
| [], I => I
| E :: Es, I =>
    updateState Es
      (Instance.update I E.live
        ((RAExpr.union (RAExpr.rel E.live)
          E.derive).eval I))

/- The explicit state produced by a complete body. -/
def resultState
    (Es : List (Entry D Γ))
    (I : Instance D Γ) : Instance D Γ :=
  updateState Es (snapshotState Es I)

private theorem snapshotState_bigStep
    (Es : List (Entry D Γ))
    (I : Instance D Γ) :
    Cmd.BigStep (Cmd.seqList (Es.map Entry.snapshotCmd))
      I (snapshotState Es I) := by
  induction Es generalizing I with
  | nil => exact Cmd.BigStep.skip I
  | cons E Es ih =>
      exact Cmd.BigStep.seq
        (Cmd.BigStep.assign I E.snapshot
          (RAExpr.relAs E.snapshot E.live E.arity_eq))
        (ih _)

private theorem updateState_bigStep
    (Es : List (Entry D Γ))
    (I : Instance D Γ) :
    Cmd.BigStep (Cmd.seqList (Es.map Entry.updateCmd))
      I (updateState Es I) := by
  induction Es generalizing I with
  | nil => exact Cmd.BigStep.skip I
  | cons E Es ih =>
      exact Cmd.BigStep.seq
        (Cmd.BigStep.assign I E.live
          (RAExpr.union (RAExpr.rel E.live) E.derive))
        (ih _)

/- The canonical body executes to the explicit result. -/
theorem canonicalBody_bigStep
    (Es : List (Entry D Γ))
    (I : Instance D Γ) :
    Cmd.BigStep (canonicalBody Es) I
      (resultState Es I) := by
  unfold canonicalBody resultState
  apply (Cmd.bigStep_seqList_append_iff _ _ _ _).mpr
  exact ⟨snapshotState Es I,
    snapshotState_bigStep Es I,
    updateState_bigStep Es (snapshotState Es I)⟩

/- A recognized source body has the explicit execution. -/
theorem body_bigStep
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (I : Instance D Γ) :
    Cmd.BigStep C I (resultState B.entries I) := by
  exact (B.body_equiv I _).mpr
    (canonicalBody_bigStep B.entries I)

private theorem snapshotState_lookup_of_not_mem
    (Es : List (Entry D Γ))
    (I : Instance D Γ) (X : Γ.syms)
    (hX : X.1 ∉ Es.map (fun E => E.snapshot.1)) :
    snapshotState Es I X = I X := by
  induction Es generalizing I with
  | nil => rfl
  | cons E Es ih =>
      simp only [List.map_cons, List.mem_cons] at hX
      rw [snapshotState, ih]
      · apply Instance.update_lookup_ne
        intro hEq
        exact hX (Or.inl (congrArg Subtype.val hEq))
      · intro hMem
        exact hX (Or.inr hMem)

private theorem updateState_lookup_of_not_mem
    (Es : List (Entry D Γ))
    (I : Instance D Γ) (X : Γ.syms)
    (hX : X.1 ∉ Es.map (fun E => E.live.1)) :
    updateState Es I X = I X := by
  induction Es generalizing I with
  | nil => rfl
  | cons E Es ih =>
      simp only [List.map_cons, List.mem_cons] at hX
      rw [updateState, ih]
      · apply Instance.update_lookup_ne
        intro hEq
        exact hX (Or.inl (congrArg Subtype.val hEq))
      · intro hMem
        exact hX (Or.inr hMem)

private theorem eval_rel
    (X : Γ.syms) (I : Instance D Γ) :
    (RAExpr.rel X).eval I = I X := by
  have h := RAExpr.raw_eval?_eq_eval (RAExpr.rel X) I
  symm
  simpa [RAExpr.rel, RawRAExpr.eval?,
    Instance.relation?, X.2] using h

private theorem oneUpdate_subset
    (E : Entry D Γ) (I : Instance D Γ) :
    I.Subset
      (Instance.update I E.live
        ((RAExpr.union (RAExpr.rel E.live)
          E.derive).eval I)) := by
  intro X t ht
  by_cases hX : X = E.live
  · subst X
    rw [Instance.update_lookup_eq,
      RAExpr.mem_eval_union_iff]
    left
    simpa [eval_rel] using ht
  · simpa [Instance.update_lookup_ne _ _ _ hX]

/- Inflationary updates grow the complete input state. -/
theorem updateState_subset
    (Es : List (Entry D Γ)) (I : Instance D Γ) :
    I.Subset (updateState Es I) := by
  induction Es generalizing I with
  | nil => exact Instance.Subset.refl I
  | cons E Es ih =>
      exact Instance.Subset.trans
        (oneUpdate_subset E I) (ih _)

end InflationaryBlock

end Whiel

------------------------------------------------------------
-- Block Invariant And Stuttering
------------------------------------------------------------

namespace Whiel

namespace InflationaryBlock

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem eval_relAs
    (X Y : Γ.syms) (hAr : Γ.arity X = Γ.arity Y)
    (I : Instance D Γ) :
    (RAExpr.relAs X Y hAr).eval I =
      cast (congrArg (FinRelation D) hAr.symm) (I Y) := by
  apply Finset.ext
  intro t
  unfold RAExpr.relAs
  rw [RAExpr.mem_eval_castArity,
    FinRelation.mem_cast_iff, eval_rel]

omit [Domain D] in
private theorem eq_cast_iff_cast_eq
    {m n : Nat} (h : m = n)
    (R : FinRelation D m) (S : FinRelation D n) :
    S = cast (congrArg (FinRelation D) h) R ↔
      cast (congrArg (FinRelation D) h.symm) S = R := by
  cases h
  simp

/- A snapshot relation viewed at its live arity. -/
def Entry.snapshotRel
    (E : Entry D Γ) (I : Instance D Γ) :
    FinRelation D (Γ.arity E.live) :=
  (RAExpr.relAs E.live E.snapshot
    E.arity_eq.symm).eval I

/- All snapshots and live relations currently agree. -/
def allEqual
    (Es : List (Entry D Γ)) (I : Instance D Γ) : Prop :=
  ∀ E ∈ Es,
    (RAExpr.relAs E.snapshot E.live
      E.arity_eq).eval I = I E.snapshot

/- The containment and closure clauses for one state. -/
def BasicInvariant
    (Es : List (Entry D Γ)) (I : Instance D Γ) : Prop :=
  (∀ E ∈ Es, I E.snapshot ⊆
    (RAExpr.relAs E.snapshot E.live
      E.arity_eq).eval I) ∧
    (allEqual Es I →
      ∀ E ∈ Es, E.derive.eval I ⊆ I E.live)

/- The local invariant is closed under repeated bodies. -/
def Block.invariant
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (I : Instance D Γ) : Prop :=
  ∀ n : Nat,
    BasicInvariant B.entries
      ((resultState B.entries)^[n] I)

private theorem equalGuard_iff_allEqualEntry
    (E : Entry D Γ) (I : Instance D Γ) :
    E.equalGuard.eval I ↔
      (RAExpr.relAs E.snapshot E.live
        E.arity_eq).eval I = I E.snapshot := by
  unfold Entry.equalGuard
  simp only [Guard.eval_eq_iff]
  rw [eval_rel, eval_relAs, eval_relAs]
  exact eq_cast_iff_cast_eq E.arity_eq
    (I E.snapshot) (I E.live)

/- A false local guard means every pair is equal. -/
theorem allEqual_of_guard_false
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (I : Instance D Γ)
    (hDone : ¬ G.eval I) :
    allEqual B.entries I := by
  have hDoneCanonical :
      ¬ (canonicalGuard B.entries).eval I := by
    intro hCanonical
    exact hDone ((B.guard_equiv I).mpr hCanonical)
  have hAnd :
      (andList
        (B.entries.map Entry.equalGuard)).eval I := by
    by_contra hFalse
    exact hDoneCanonical hFalse
  intro E hE
  apply (equalGuard_iff_allEqualEntry E I).mp
  exact (andList_eval_iff _ _).mp hAnd
    E.equalGuard (List.mem_map.mpr ⟨E, hE, rfl⟩)

private theorem snapshotState_eq_of_allEqual
    (Es : List (Entry D Γ)) (I : Instance D Γ)
    (hEq : allEqual Es I) :
    snapshotState Es I = I := by
  induction Es generalizing I with
  | nil => rfl
  | cons E Es ih =>
      have hHead := hEq E (by simp)
      rw [snapshotState, hHead, Instance.update_cancel]
      apply ih
      intro F hF
      exact hEq F (by simp [hF])

private theorem union_eval_eq_of_subset
    (E : Entry D Γ) (I : Instance D Γ)
    (hSub : E.derive.eval I ⊆ I E.live) :
    (RAExpr.union (RAExpr.rel E.live) E.derive).eval I =
      I E.live := by
  apply Finset.ext
  intro t
  rw [RAExpr.mem_eval_union_iff, eval_rel]
  constructor
  · rintro (ht | ht)
    · exact ht
    · exact hSub ht
  · intro ht
    exact Or.inl ht

private theorem updateState_eq_of_closed
    (Es : List (Entry D Γ)) (I : Instance D Γ)
    (hClosed : ∀ E ∈ Es,
      E.derive.eval I ⊆ I E.live) :
    updateState Es I = I := by
  induction Es generalizing I with
  | nil => rfl
  | cons E Es ih =>
      have hHead := hClosed E (by simp)
      rw [updateState, union_eval_eq_of_subset E I hHead,
        Instance.update_cancel]
      apply ih
      intro F hF
      exact hClosed F (by simp [hF])

/- Closure and pair equality make the body a no-op. -/
theorem resultState_eq_of_basic_guard_false
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (I : Instance D Γ)
    (hInv : BasicInvariant B.entries I)
    (hDone : ¬ G.eval I) :
    resultState B.entries I = I := by
  have hEq := allEqual_of_guard_false B I hDone
  have hSnap := snapshotState_eq_of_allEqual
    B.entries I hEq
  rw [resultState, hSnap]
  exact updateState_eq_of_closed B.entries I (hInv.2 hEq)

/- The block invariant is preserved by source execution. -/
theorem body_invariant
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) {I J : Instance D Γ}
    (hInv : B.invariant I)
    (hStep : Cmd.BigStep C I J) :
    B.invariant J := by
  have hResult : J = resultState B.entries I :=
    Cmd.BigStep.deterministic hStep (body_bigStep B I)
  subst J
  intro n
  simpa [Function.iterate_succ_apply] using hInv (n + 1)

/- Invariant plus a false guard gives exact stuttering. -/
theorem body_stutter
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) {I : Instance D Γ}
    (hInv : B.invariant I)
    (hDone : ¬ G.eval I) :
    Cmd.BigStep C I I := by
  have hBasic : BasicInvariant B.entries I := by
    simpa using hInv 0
  have hEq := resultState_eq_of_basic_guard_false
    B I hBasic hDone
  conv_rhs => rw [← hEq]
  exact body_bigStep B I

end InflationaryBlock

end Whiel

------------------------------------------------------------
-- Growth And Framing
------------------------------------------------------------

namespace Whiel

namespace InflationaryBlock

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem oneSnapshot_subset
    (E : Entry D Γ) (I : Instance D Γ)
    (hSub : I E.snapshot ⊆
      (RAExpr.relAs E.snapshot E.live
        E.arity_eq).eval I) :
    I.Subset
      (Instance.update I E.snapshot
        ((RAExpr.relAs E.snapshot E.live
          E.arity_eq).eval I)) := by
  intro X t ht
  by_cases hX : X = E.snapshot
  · subst X
    simpa using hSub ht
  · simpa [Instance.update_lookup_ne _ _ _ hX]

private theorem snapshotState_subset_of
    (Es : List (Entry D Γ)) (I : Instance D Γ)
    (hNodup :
      (Es.map fun E => E.snapshot.1).Nodup)
    (hDisjoint :
      ∀ E ∈ Es, ∀ F ∈ Es,
        E.snapshot.1 ≠ F.live.1)
    (hContain :
      ∀ E ∈ Es, I E.snapshot ⊆
        (RAExpr.relAs E.snapshot E.live
          E.arity_eq).eval I) :
    I.Subset (snapshotState Es I) := by
  induction Es generalizing I with
  | nil => exact Instance.Subset.refl I
  | cons E Es ih =>
      have hHead := hContain E (by simp)
      let J := Instance.update I E.snapshot
        ((RAExpr.relAs E.snapshot E.live
          E.arity_eq).eval I)
      have hIJ : I.Subset J := oneSnapshot_subset E I hHead
      have hTailContain :
          ∀ F ∈ Es, J F.snapshot ⊆
            (RAExpr.relAs F.snapshot F.live
              F.arity_eq).eval J := by
        intro F hF
        have hSnapRaw : F.snapshot.1 ≠ E.snapshot.1 := by
          intro hEq
          exact (List.nodup_cons.mp hNodup).1
            (List.mem_map.mpr
              ⟨F, hF, hEq⟩)
        have hSnap : F.snapshot ≠ E.snapshot := by
          intro hEq
          exact hSnapRaw (congrArg Subtype.val hEq)
        have hLiveRaw : E.snapshot.1 ≠ F.live.1 :=
          hDisjoint E (by simp) F (by simp [hF])
        have hLive : F.live ≠ E.snapshot := by
          intro hEq
          exact hLiveRaw (congrArg Subtype.val hEq).symm
        have hJSnapshot : J F.snapshot = I F.snapshot := by
          dsimp [J]
          exact Instance.update_lookup_ne _ _ _ hSnap _
        have hJLive : J F.live = I F.live := by
          dsimp [J]
          exact Instance.update_lookup_ne _ _ _ hLive _
        rw [hJSnapshot, eval_relAs, hJLive]
        have hOriginal := hContain F (by simp [hF])
        rw [eval_relAs] at hOriginal
        exact hOriginal
      have hTailDisjoint :
          ∀ F ∈ Es, ∀ K ∈ Es,
            F.snapshot.1 ≠ K.live.1 := by
        intro F hF K hK
        exact hDisjoint F (by simp [hF]) K (by simp [hK])
      have hJK : J.Subset (snapshotState Es J) :=
        ih J (List.nodup_cons.mp hNodup).2
          hTailDisjoint hTailContain
      exact Instance.Subset.trans hIJ hJK

/- Every live accumulator grows, without positivity. -/
theorem live_grows
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (I : Instance D Γ)
    (E : Entry D Γ) (hE : E ∈ B.entries) :
    I E.live ⊆ resultState B.entries I E.live := by
  have hNotSnapshot :
      E.live.1 ∉
        B.entries.map (fun F => F.snapshot.1) := by
    intro hMem
    rcases List.mem_map.mp hMem with ⟨F, hF, hEq⟩
    exact B.targets_disjoint F hF E hE hEq
  have hUpdate :=
    updateState_subset B.entries
      (snapshotState B.entries I) E.live
  rw [snapshotState_lookup_of_not_mem
    B.entries I E.live hNotSnapshot] at hUpdate
  exact hUpdate

/- Under the invariant, the complete instance grows. -/
theorem resultState_subset
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (I : Instance D Γ)
    (hInv : B.invariant I) :
    I.Subset (resultState B.entries I) := by
  have hBasic : BasicInvariant B.entries I := by
    simpa using hInv 0
  have hSnapshots :
      I.Subset (snapshotState B.entries I) :=
    snapshotState_subset_of B.entries I
      B.snapshot_nodup B.targets_disjoint hBasic.1
  exact Instance.Subset.trans hSnapshots
    (updateState_subset B.entries
      (snapshotState B.entries I))

/- Under the invariant, every snapshot relation grows. -/
theorem snapshot_grows
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (I : Instance D Γ)
    (hInv : B.invariant I)
    (E : Entry D Γ) (_hE : E ∈ B.entries) :
    I E.snapshot ⊆
      resultState B.entries I E.snapshot :=
  resultState_subset B I hInv E.snapshot

private theorem mem_targets_iff
    (Es : List (Entry D Γ)) (X : A) :
    X ∈ Block.targets Es ↔
      ∃ E ∈ Es, X = E.snapshot.1 ∨ X = E.live.1 := by
  induction Es with
  | nil => simp [Block.targets]
  | cons E Es ih =>
      simp [Block.targets, ih]
      aesop

/- Relations outside the write targets are unchanged. -/
theorem outside_writeTargets_unchanged
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (I : Instance D Γ)
    (X : Γ.syms) (hX : X.1 ∉ B.writeTargets) :
    resultState B.entries I X = I X := by
  have hSnapshots :
      X.1 ∉ B.entries.map (fun E => E.snapshot.1) := by
    intro hMem
    rcases List.mem_map.mp hMem with ⟨E, hE, hEq⟩
    apply hX
    apply (mem_targets_iff B.entries X.1).mpr
    exact ⟨E, hE, Or.inl hEq.symm⟩
  have hLives :
      X.1 ∉ B.entries.map (fun E => E.live.1) := by
    intro hMem
    rcases List.mem_map.mp hMem with ⟨E, hE, hEq⟩
    apply hX
    apply (mem_targets_iff B.entries X.1).mpr
    exact ⟨E, hE, Or.inr hEq.symm⟩
  rw [resultState,
    updateState_lookup_of_not_mem _ _ _ hLives,
    snapshotState_lookup_of_not_mem _ _ _ hSnapshots]

end InflationaryBlock

end Whiel

------------------------------------------------------------
-- Invariant Locality
------------------------------------------------------------

namespace Whiel

namespace InflationaryBlock

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem mem_allSymbols_iff
    (Es : List (Entry D Γ)) (X : A) :
    X ∈ Block.allSymbols Es ↔
      ∃ E ∈ Es,
        X = E.snapshot.1 ∨ X = E.live.1 ∨
          X ∈ E.dependencies := by
  induction Es with
  | nil => simp [Block.allSymbols]
  | cons E Es ih =>
      simp [Block.allSymbols, ih]
      aesop

private theorem entry_snapshot_mem_footprint
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (E : Entry D Γ)
    (hE : E ∈ B.entries) :
    E.snapshot.1 ∈ B.footprint := by
  apply (mem_allSymbols_iff B.entries _).mpr
  exact ⟨E, hE, Or.inl rfl⟩

private theorem entry_live_mem_footprint
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (E : Entry D Γ)
    (hE : E ∈ B.entries) :
    E.live.1 ∈ B.footprint := by
  apply (mem_allSymbols_iff B.entries _).mpr
  exact ⟨E, hE, Or.inr (Or.inl rfl)⟩

private theorem entry_dependencies_subset_footprint
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) (E : Entry D Γ)
    (hE : E ∈ B.entries) :
    E.dependencies ⊆ B.footprint := by
  intro X hX
  apply (mem_allSymbols_iff B.entries _).mpr
  exact ⟨E, hE, Or.inr (Or.inr hX)⟩

private theorem snapshotState_agree
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C)
    (Es : List (Entry D Γ))
    (hEs : ∀ E ∈ Es, E ∈ B.entries)
    {I J : Instance D Γ}
    (hAgree : Instance.agreeOn B.footprint I J) :
    Instance.agreeOn B.footprint
      (snapshotState Es I) (snapshotState Es J) := by
  induction Es generalizing I J with
  | nil => exact hAgree
  | cons E Es ih =>
      have hE : E ∈ B.entries := hEs E (by simp)
      have hLive := hAgree E.live
        (entry_live_mem_footprint B E hE)
      have hValue :
          (RAExpr.relAs E.snapshot E.live
              E.arity_eq).eval I =
            (RAExpr.relAs E.snapshot E.live
              E.arity_eq).eval J := by
        rw [eval_relAs, eval_relAs, hLive]
      have hUpdated : Instance.agreeOn B.footprint
          (Instance.update I E.snapshot
            ((RAExpr.relAs E.snapshot E.live
              E.arity_eq).eval I))
          (Instance.update J E.snapshot
            ((RAExpr.relAs E.snapshot E.live
              E.arity_eq).eval J)) := by
        intro X hX
        by_cases hXE : X = E.snapshot
        · subst X
          simp [hValue]
        · simp [Instance.update_lookup_ne, hXE,
            hAgree X hX]
      apply ih
      · intro F hF
        exact hEs F (by simp [hF])
      · exact hUpdated

private theorem updateState_agree
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C)
    (Es : List (Entry D Γ))
    (hEs : ∀ E ∈ Es, E ∈ B.entries)
    {I J : Instance D Γ}
    (hAgree : Instance.agreeOn B.footprint I J) :
    Instance.agreeOn B.footprint
      (updateState Es I) (updateState Es J) := by
  induction Es generalizing I J with
  | nil => exact hAgree
  | cons E Es ih =>
      have hE : E ∈ B.entries := hEs E (by simp)
      have hLive := hAgree E.live
        (entry_live_mem_footprint B E hE)
      have hDerive : E.derive.eval I = E.derive.eval J := by
        apply RAExpr.eval_eq_of_agreeOn E.derive
        intro X hX
        exact hAgree X
          (entry_dependencies_subset_footprint B E hE hX)
      have hValue :
          (RAExpr.union (RAExpr.rel E.live)
              E.derive).eval I =
            (RAExpr.union (RAExpr.rel E.live)
              E.derive).eval J := by
        apply Finset.ext
        intro t
        rw [RAExpr.mem_eval_union_iff,
          RAExpr.mem_eval_union_iff,
          eval_rel, eval_rel, hLive, hDerive]
      have hUpdated : Instance.agreeOn B.footprint
          (Instance.update I E.live
            ((RAExpr.union (RAExpr.rel E.live)
              E.derive).eval I))
          (Instance.update J E.live
            ((RAExpr.union (RAExpr.rel E.live)
              E.derive).eval J)) := by
        intro X hX
        by_cases hXE : X = E.live
        · subst X
          simp [hValue]
        · simp [Instance.update_lookup_ne, hXE,
            hAgree X hX]
      apply ih
      · intro F hF
        exact hEs F (by simp [hF])
      · exact hUpdated

private theorem resultState_agree
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) {I J : Instance D Γ}
    (hAgree : Instance.agreeOn B.footprint I J) :
    Instance.agreeOn B.footprint
      (resultState B.entries I)
      (resultState B.entries J) := by
  apply updateState_agree B B.entries (by simp)
  exact snapshotState_agree B B.entries (by simp) hAgree

private theorem basicInvariant_congr
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) {I J : Instance D Γ}
    (hAgree : Instance.agreeOn B.footprint I J) :
    BasicInvariant B.entries I ↔
      BasicInvariant B.entries J := by
  have hSnapshot : ∀ E ∈ B.entries,
      I E.snapshot = J E.snapshot := by
    intro E hE
    exact hAgree E.snapshot
      (entry_snapshot_mem_footprint B E hE)
  have hLive : ∀ E ∈ B.entries,
      I E.live = J E.live := by
    intro E hE
    exact hAgree E.live
      (entry_live_mem_footprint B E hE)
  have hDerive : ∀ E ∈ B.entries,
      E.derive.eval I = E.derive.eval J := by
    intro E hE
    apply RAExpr.eval_eq_of_agreeOn E.derive
    intro X hX
    exact hAgree X
      (entry_dependencies_subset_footprint B E hE hX)
  have hEqual : allEqual B.entries I ↔
      allEqual B.entries J := by
    constructor
    · intro hEq E hE
      have h := hEq E hE
      rw [eval_relAs] at h
      rw [eval_relAs]
      simpa [hLive E hE, hSnapshot E hE] using h
    · intro hEq E hE
      have h := hEq E hE
      rw [eval_relAs] at h
      rw [eval_relAs]
      rw [hLive E hE, hSnapshot E hE]
      exact h
  constructor
  · rintro ⟨hContain, hClosed⟩
    constructor
    · intro E hE
      have h := hContain E hE
      rw [eval_relAs] at h
      rw [eval_relAs]
      simpa [hSnapshot E hE, hLive E hE] using h
    · intro hEq E hE
      rw [← hDerive E hE, ← hLive E hE]
      exact hClosed (hEqual.mpr hEq) E hE
  · rintro ⟨hContain, hClosed⟩
    constructor
    · intro E hE
      have h := hContain E hE
      rw [eval_relAs] at h
      rw [eval_relAs]
      rw [hSnapshot E hE, hLive E hE]
      exact h
    · intro hEq E hE
      rw [hDerive E hE, hLive E hE]
      exact hClosed (hEqual.mp hEq) E hE

private theorem iterate_result_agree
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) {I J : Instance D Γ}
    (hAgree : Instance.agreeOn B.footprint I J) :
    ∀ n, Instance.agreeOn B.footprint
      ((resultState B.entries)^[n] I)
      ((resultState B.entries)^[n] J) := by
  intro n
  induction n with
  | zero => exact hAgree
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using
        resultState_agree B ih

/- The block invariant depends only on its footprint. -/
theorem invariant_local
    {G : Guard D Γ} {C : Cmd D Γ}
    (B : Block G C) {I J : Instance D Γ}
    (hAgree : Instance.agreeOn B.footprint I J) :
    B.invariant I ↔ B.invariant J := by
  constructor
  · intro hInv n
    exact (basicInvariant_congr B
      (iterate_result_agree B hAgree n)).mp (hInv n)
  · intro hInv n
    exact (basicInvariant_congr B
      (iterate_result_agree B hAgree n)).mpr (hInv n)

end InflationaryBlock

end Whiel
