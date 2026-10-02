-- Author: Jesse Comer
import Whiel.Cmd.Rewrites
import Whiel.Cmd.Rewrites.FramedLoop
import Whiel.RelationNames.NameSupply

/-
  Two-loop flattening for Whiel commands.

  This file lowers a sequential composition of two recognized
  framed loops to a single framed-loop command over an
  extended execution schema.  The extension adds two hidden
  nullary relation symbols used as phase flags.

  Key definitions include:
    * `Whiel.Cmd.onExtension`
    * `Whiel.TwoLoopFlat.execSchema`
    * `Whiel.TwoLoopFlat.commandOfParts`
    * `Whiel.TwoLoopFlat.programOfParts`
    * `Whiel.TwoLoopFlat.flattenSeq?`
    * `Whiel.TwoLoopFlat.flattenCommand?`
-/

------------------------------------------------------------
-- Command Retagging
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/- Reinterpret a command over an extending schema. -/
def onExtension
    (hExt : Ω.extensionOf Γ) :
    Cmd D Γ → Cmd D Ω
| .skip =>
    .skip
| .assign X e =>
    .assign
      (UnnamedSchema.symOfExtension hExt X)
      (RAExpr.castArity
        (UnnamedSchema.arity_eq_of_extensionOf hExt X)
        (e.onExtension hExt))
| .seq C₁ C₂ =>
    .seq (onExtension hExt C₁) (onExtension hExt C₂)
| .ite G C₁ C₂ =>
    .ite
      (G.onExtension hExt)
      (onExtension hExt C₁)
      (onExtension hExt C₂)
| .while G C =>
    .while (G.onExtension hExt) (onExtension hExt C)

/- Retagging preserves assigned raw relation names. -/
@[simp] theorem assignedSymbols_onExtension
    (hExt : Ω.extensionOf Γ)
    (C : Cmd D Γ) :
    (C.onExtension hExt).assignedSymbols =
      C.assignedSymbols := by
  induction C with
  | skip =>
      simp [onExtension, assignedSymbols]
  | assign X e =>
      simp [onExtension, assignedSymbols,
        UnnamedSchema.symOfExtension]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [onExtension, assignedSymbols, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [onExtension, assignedSymbols, ih₁, ih₂]
  | «while» G C ih =>
      simp [onExtension, assignedSymbols, ih]

/- Retagging preserves loop-freedom. -/
theorem loopFree_onExtension
    (hExt : Ω.extensionOf Γ)
    (C : Cmd D Γ) :
    (C.onExtension hExt).LoopFree ↔ C.LoopFree := by
  induction C with
  | skip =>
      simp [onExtension, LoopFree]
  | assign X e =>
      simp [onExtension, LoopFree]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [onExtension, LoopFree, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [onExtension, LoopFree, ih₁, ih₂]
  | «while» G C ih =>
      simp [onExtension, LoopFree]

/- Cleaning one sequence preserves loop-freedom. -/
theorem loopFree_cleanSeq
    (C₁ C₂ : Cmd D Γ) :
    (cleanSeq C₁ C₂).LoopFree ↔
      C₁.LoopFree ∧ C₂.LoopFree := by
  induction C₁ generalizing C₂
  <;> cases C₂
  <;> simp [cleanSeq, LoopFree, *, and_assoc]

/- Cleaning preserves loop-freedom. -/
theorem loopFree_clean
    (C : Cmd D Γ) :
    C.clean.LoopFree ↔ C.LoopFree := by
  induction C with
  | skip =>
      simp [clean, LoopFree]
  | assign X e =>
      simp [clean, LoopFree]
  | seq C₁ C₂ ih₁ ih₂ =>
      rw [clean]
      rw [loopFree_cleanSeq]
      exact and_congr ih₁ ih₂
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [clean, LoopFree, ih₁, ih₂]
  | «while» G C ih =>
      simp [clean, LoopFree]

/- A sequenced command list is loop-free exactly when all
  list elements are loop-free. -/
theorem loopFree_seqList_iff
    (Cs : List (Cmd D Γ)) :
    (seqList Cs).LoopFree ↔
      ∀ C ∈ Cs, C.LoopFree := by
  induction Cs with
  | nil =>
      simp [seqList, LoopFree]
  | cons C Cs ih =>
      simp [seqList, LoopFree, ih]

/- Retagged commands preserve symbols not assigned by the
  source command. -/
theorem onExtension_preserves_new_symbols
    {hExt : Ω.extensionOf Γ}
    {C : Cmd D Γ}
    {I J : Instance D Ω}
    (hStep : BigStep (C.onExtension hExt) I J)
    (X : Ω.syms)
    (hX : X.1 ∉ C.assignedSymbols) :
    J X = I X := by
  exact BigStep.no_update_preservation
    hStep X (by simpa using hX)

end Cmd

end Whiel

------------------------------------------------------------
-- Reduct/Update Support
------------------------------------------------------------

namespace Instance

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/- Updating an old symbol before reduct is the same as
  reducing first and updating the old symbol. -/
theorem reduct_update_of_mem
    (hExt : Ω.extensionOf Γ)
    (J : Instance D Ω)
    (X : Γ.syms)
    (R :
      FinRelation D
        (Ω.arity (UnnamedSchema.symOfExtension hExt X))) :
    Instance.reduct hExt
        (Instance.update J
          (UnnamedSchema.symOfExtension hExt X) R) =
      Instance.update
        (Instance.reduct hExt J)
        X
        (cast
          (congrArg (FinRelation D)
            (UnnamedSchema.arity_eq_of_extensionOf
              hExt X))
          R) := by
  apply Instance.ext
  intro Y
  by_cases hYX : Y = X
  · subst hYX
    unfold Instance.reduct
    simp [Instance.update_lookup_eq,
      UnnamedSchema.symOfExtension]
  · have hNe :
        UnnamedSchema.symOfExtension hExt Y ≠
          UnnamedSchema.symOfExtension hExt X := by
      intro hEq
      apply hYX
      exact Subtype.ext
        (congrArg (fun Z : Ω.syms => Z.1) hEq)
    have hNe' :
        (⟨Y.1, hExt.1 Y.2⟩ : Ω.syms) ≠
          UnnamedSchema.symOfExtension hExt X := by
      simpa [UnnamedSchema.symOfExtension] using hNe
    unfold Instance.reduct
    simp [Instance.update_lookup_ne, hNe', hYX]

/- Empty expansion along the reflexive extension is the
  original instance. -/
theorem expandEmpty_refl
    (I : Instance D Γ) :
    Instance.expandEmpty
        (UnnamedSchema.extensionOf_refl Γ) I = I := by
  apply Instance.ext
  intro X
  unfold Instance.expandEmpty Instance.relationOfExtension
  simp [X.2]

end Instance

namespace RAExpr

variable {A D : Type}
variable {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

/- Evaluating an arity-cast expression and casting the
  relation back gives the original evaluation. -/
theorem cast_eval_castArity
    {m n : Nat}
    (h : m = n)
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    cast (congrArg (FinRelation D) h)
        ((RAExpr.castArity h e).eval I) =
      e.eval I := by
  cases h
  rfl

end RAExpr

------------------------------------------------------------
-- Phase Schemas
------------------------------------------------------------

namespace Whiel

namespace TwoLoopFlat

variable {A : Type}
variable [RelationNameSupply A]

/- First phase-flag name. -/
def phase₁Name
    (base : A)
    (Γ : UnnamedSchema A) :
    A :=
  RelationNameSupply.freshName base Γ.syms

/- The first phase flag is fresh for the source schema. -/
theorem phase₁_fresh
    (base : A)
    (Γ : UnnamedSchema A) :
    phase₁Name base Γ ∉ Γ.syms := by
  exact RelationNameSupply.freshName_fresh base Γ.syms

/- Source schema extended by the first phase flag. -/
def phase₁Schema
    (base : A)
    (Γ : UnnamedSchema A) :
    UnnamedSchema A :=
  Γ.insertFresh (phase₁Name base Γ) 0
    (phase₁_fresh base Γ)

/- Second phase-flag name. -/
def phase₂Name
    (base : A)
    (Γ : UnnamedSchema A) :
    A :=
  RelationNameSupply.freshName base
    (insert (phase₁Name base Γ) Γ.syms)

/- The second phase flag is fresh for the first extension. -/
theorem phase₂_fresh_phase₁
    (base : A)
    (Γ : UnnamedSchema A) :
    phase₂Name base Γ ∉ (phase₁Schema base Γ).syms := by
  unfold phase₂Name phase₁Schema
  simpa [UnnamedSchema.insertFresh] using
    RelationNameSupply.freshName_fresh base
      (insert
        (RelationNameSupply.freshName base Γ.syms)
        Γ.syms)

/- The second phase flag is fresh for the source schema. -/
theorem phase₂_fresh
    (base : A)
    (Γ : UnnamedSchema A) :
    phase₂Name base Γ ∉ Γ.syms := by
  have hFresh :=
    RelationNameSupply.freshName_fresh base
      (insert (phase₁Name base Γ) Γ.syms)
  intro hMem
  exact hFresh (Finset.mem_insert.mpr (Or.inr hMem))

/- The two phase flags are distinct. -/
theorem phase₂_ne_phase₁
    (base : A)
    (Γ : UnnamedSchema A) :
    phase₂Name base Γ ≠ phase₁Name base Γ := by
  have hFresh :=
    RelationNameSupply.freshName_fresh base
      (insert (phase₁Name base Γ) Γ.syms)
  intro hEq
  exact hFresh (Finset.mem_insert.mpr (Or.inl hEq))

/- Execution schema with both hidden phase flags. -/
def execSchema
    (base : A)
    (Γ : UnnamedSchema A) :
    UnnamedSchema A :=
  (phase₁Schema base Γ).insertFresh
    (phase₂Name base Γ) 0
    (phase₂_fresh_phase₁ base Γ)

/- The final schema extends the first phase schema. -/
theorem execSchema_extension_phase₁
    (base : A)
    (Γ : UnnamedSchema A) :
    (execSchema base Γ).extensionOf
      (phase₁Schema base Γ) := by
  exact UnnamedSchema.insertFresh_extensionOf
    (phase₁Schema base Γ)
    (phase₂Name base Γ) 0
    (phase₂_fresh_phase₁ base Γ)

/- The final schema extends the source schema. -/
theorem execSchema_extension
    (base : A)
    (Γ : UnnamedSchema A) :
    (execSchema base Γ).extensionOf Γ := by
  exact UnnamedSchema.extensionOf_trans
    (execSchema_extension_phase₁ base Γ)
    (UnnamedSchema.insertFresh_extensionOf
      Γ (phase₁Name base Γ) 0
      (phase₁_fresh base Γ))

/- First phase flag as an execution-schema symbol. -/
def phase₁Sym
    (base : A)
    (Γ : UnnamedSchema A) :
    (execSchema base Γ).syms :=
  UnnamedSchema.symOfExtension
    (execSchema_extension_phase₁ base Γ)
    (Γ.insertedSym
      (phase₁Name base Γ) 0
      (phase₁_fresh base Γ))

/- Second phase flag as an execution-schema symbol. -/
def phase₂Sym
    (base : A)
    (Γ : UnnamedSchema A) :
    (execSchema base Γ).syms :=
  (phase₁Schema base Γ).insertedSym
    (phase₂Name base Γ) 0
    (phase₂_fresh_phase₁ base Γ)

/- The execution-schema phase symbols are distinct. -/
theorem phase₁Sym_ne_phase₂Sym
    (base : A)
    (Γ : UnnamedSchema A) :
    phase₁Sym base Γ ≠ phase₂Sym base Γ := by
  intro hEq
  exact phase₂_ne_phase₁ base Γ
    (by
      have hRaw :=
        congrArg (fun X : (execSchema base Γ).syms => X.1)
          hEq
      simpa [phase₁Sym, phase₂Sym,
        UnnamedSchema.symOfExtension,
        UnnamedSchema.insertedSym] using hRaw.symm)

/- The first phase flag is nullary. -/
theorem phase₁_arity
    (base : A)
    (Γ : UnnamedSchema A) :
    (execSchema base Γ).arity
      (phase₁Sym base Γ) = 0 := by
  let X : (phase₁Schema base Γ).syms :=
    Γ.insertedSym
      (phase₁Name base Γ) 0
      (phase₁_fresh base Γ)
  change
    (execSchema base Γ).arity
      (UnnamedSchema.symOfExtension
        (execSchema_extension_phase₁ base Γ) X) = 0
  have hAr :=
    UnnamedSchema.arity_eq_of_extensionOf
      (execSchema_extension_phase₁ base Γ) X
  have hX : (phase₁Schema base Γ).arity X = 0 := by
    simp [X, phase₁Schema]
  simpa [UnnamedSchema.symOfExtension] using hAr.trans hX

/- The second phase flag is nullary. -/
theorem phase₂_arity
    (base : A)
    (Γ : UnnamedSchema A) :
    (execSchema base Γ).arity
      (phase₂Sym base Γ) = 0 := by
  simp [phase₂Sym, execSchema]

end TwoLoopFlat

end Whiel

------------------------------------------------------------
-- Phase Commands
------------------------------------------------------------

namespace Whiel

namespace TwoLoopFlat

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Cast the nullary singleton to a phase symbol arity. -/
def trueExpr
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (hAr : Ω.arity X = 0) :
    RAExpr D Ω (Ω.arity X) :=
  RAExpr.castArity hAr (RAExpr.top : RAExpr D Ω 0)

/- Cast the nullary empty relation to a phase symbol arity. -/
def falseExpr
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (hAr : Ω.arity X = 0) :
    RAExpr D Ω (Ω.arity X) :=
  RAExpr.castArity hAr (RAExpr.empty (D := D) 0)

/- Test that a phase flag is true. -/
def flagGuard
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (hAr : Ω.arity X = 0) :
    Guard D Ω :=
  .eq (RAExpr.rel X) (trueExpr X hAr)

/- Assign true to a phase flag. -/
def assignTrue
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (hAr : Ω.arity X = 0) :
    Cmd D Ω :=
  .assign X (trueExpr X hAr)

/- Assign false to a phase flag. -/
def assignFalse
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (hAr : Ω.arity X = 0) :
    Cmd D Ω :=
  .assign X (falseExpr X hAr)

/- Evaluating a relation expression returns the instance
  relation. -/
theorem eval_rel
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (J : Instance D Ω) :
    (RAExpr.rel X).eval J = J X := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval
      (RAExpr.rel X : RAExpr D Ω (Ω.arity X)) J
  have hRaw :
      (RAExpr.rel X : RAExpr D Ω (Ω.arity X)).expr.eval?
          (Γ := Ω) J =
        some ⟨Ω.arity X, J X⟩ := by
    simp [RAExpr.rel, RawRAExpr.eval?,
      Instance.relation?, X.2]
  rw [hRaw] at hSpec
  injection hSpec with hSigma
  injection hSigma with _ hRel
  exact hRel.symm

/- The true phase expression evaluates to nullary top. -/
theorem trueExpr_eval
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (hAr : Ω.arity X = 0)
    (J : Instance D Ω) :
    (trueExpr (D := D) X hAr).eval J =
      cast (congrArg (FinRelation D) hAr.symm)
        FinRelation.top := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval
      (trueExpr (D := D) X hAr) J
  have hRaw :
      (trueExpr (D := D) X hAr).expr.eval?
          (Γ := Ω) J =
        some ⟨0, FinRelation.top⟩ := by
    simp [trueExpr, RAExpr.castArity, RAExpr.top,
      RawRAExpr.eval?]
  rw [hRaw] at hSpec
  injection hSpec with hSigma
  injection hSigma with hEq hRel
  exact eq_cast_iff_heq.mpr hRel.symm

/- The false phase expression evaluates to the nullary empty
  relation. -/
theorem falseExpr_eval
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (hAr : Ω.arity X = 0)
    (J : Instance D Ω) :
    (falseExpr (D := D) X hAr).eval J =
      cast (congrArg (FinRelation D) hAr.symm)
        (∅ : FinRelation D 0) := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval
      (falseExpr (D := D) X hAr) J
  have hRaw :
      (falseExpr (D := D) X hAr).expr.eval?
          (Γ := Ω) J =
        some ⟨0, (∅ : FinRelation D 0)⟩ := by
    simp [falseExpr, RAExpr.castArity, RAExpr.empty,
      RawRAExpr.eval?]
  rw [hRaw] at hSpec
  injection hSpec with hSigma
  injection hSigma with hEq hRel
  exact eq_cast_iff_heq.mpr hRel.symm

/- Nullary false and true phase expressions evaluate
  differently. -/
theorem falseExpr_eval_ne_trueExpr_eval
    {Ω : UnnamedSchema A}
    (X : Ω.syms)
    (hAr : Ω.arity X = 0)
    (J K : Instance D Ω) :
    (falseExpr (D := D) X hAr).eval J ≠
      (trueExpr (D := D) X hAr).eval K := by
  rw [falseExpr_eval, trueExpr_eval]
  intro hEq
  have hBack :
      (∅ : FinRelation D 0) = FinRelation.top := by
    have hCong :=
      congrArg
        (fun R : FinRelation D (Ω.arity X) =>
          cast (congrArg (FinRelation D) hAr) R)
        hEq
    simpa using hCong
  have hMem :
      Tuple.empty ∈ (∅ : FinRelation D 0) := by
    rw [hBack]
    simp [FinRelation.top]
  simp at hMem

/- First phase flag guard. -/
def phase₁Guard
    (base : A)
    (Γ : UnnamedSchema A) :
    Guard D (execSchema base Γ) :=
  flagGuard
    (phase₁Sym base Γ)
    (phase₁_arity base Γ)

/- Second phase flag guard. -/
def phase₂Guard
    (base : A)
    (Γ : UnnamedSchema A) :
    Guard D (execSchema base Γ) :=
  flagGuard
    (phase₂Sym base Γ)
    (phase₂_arity base Γ)

/- Guard for the combined dispatcher loop. -/
def loopGuard
    (base : A)
    (Γ : UnnamedSchema A) :
    Guard D (execSchema base Γ) :=
  Guard.cleanOr
    (phase₁Guard (D := D) base Γ)
    (phase₂Guard (D := D) base Γ)

/- Set the first phase flag to true. -/
def setPhase₁True
    (base : A)
    (Γ : UnnamedSchema A) :
    Cmd D (execSchema base Γ) :=
  assignTrue
    (phase₁Sym base Γ)
    (phase₁_arity base Γ)

/- Set the first phase flag to false. -/
def setPhase₁False
    (base : A)
    (Γ : UnnamedSchema A) :
    Cmd D (execSchema base Γ) :=
  assignFalse
    (phase₁Sym base Γ)
    (phase₁_arity base Γ)

/- Set the second phase flag to true. -/
def setPhase₂True
    (base : A)
    (Γ : UnnamedSchema A) :
    Cmd D (execSchema base Γ) :=
  assignTrue
    (phase₂Sym base Γ)
    (phase₂_arity base Γ)

/- Set the second phase flag to false. -/
def setPhase₂False
    (base : A)
    (Γ : UnnamedSchema A) :
    Cmd D (execSchema base Γ) :=
  assignFalse
    (phase₂Sym base Γ)
    (phase₂_arity base Γ)

end TwoLoopFlat

end Whiel

------------------------------------------------------------
-- Two-Loop Construction
------------------------------------------------------------

namespace Whiel

namespace TwoLoopFlat

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Retag a cleaned source command to the execution schema. -/
def liftCmd
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ) :
    Cmd D (execSchema base Γ) :=
  C.clean.onExtension (execSchema_extension base Γ)

/- Retag a cleaned source guard to the execution schema. -/
def liftGuard
    (base : A)
    (Γ : UnnamedSchema A)
    (G : Guard D Γ) :
    Guard D (execSchema base Γ) :=
  G.clean.onExtension (execSchema_extension base Γ)

/- Commands that initialize the dispatcher phase flags. -/
def initBlock
    (base : A)
    (Init₁ : Cmd D Γ) :
    Cmd D (execSchema base Γ) :=
  Cmd.seqList
    [ liftCmd base Γ Init₁,
      setPhase₁True (D := D) base Γ,
      setPhase₂False (D := D) base Γ ]

/- Branch that exits the first source loop. -/
def finishFirstBranch
    (base : A)
    (Close₁ Init₂ : Cmd D Γ) :
    Cmd D (execSchema base Γ) :=
  Cmd.seqList
    [ liftCmd base Γ Close₁,
      liftCmd base Γ Init₂,
      setPhase₁False (D := D) base Γ,
      setPhase₂True (D := D) base Γ ]

/- Dispatcher branch for the first source loop. -/
def phase₁Branch
    (base : A)
    (G₁ : Guard D Γ)
    (Body₁ Close₁ Init₂ : Cmd D Γ) :
    Cmd D (execSchema base Γ) :=
  .ite
    (liftGuard base Γ G₁)
    (liftCmd base Γ Body₁)
    (finishFirstBranch base Close₁ Init₂)

/- Dispatcher branch for the second source loop. -/
def phase₂Branch
    (base : A)
    (G₂ : Guard D Γ)
    (Body₂ : Cmd D Γ) :
    Cmd D (execSchema base Γ) :=
  .ite
    (liftGuard base Γ G₂)
    (liftCmd base Γ Body₂)
    (setPhase₂False (D := D) base Γ)

/- Loop-free dispatcher body. -/
def loopBody
    (base : A)
    (G₁ : Guard D Γ)
    (Body₁ Close₁ Init₂ : Cmd D Γ)
    (G₂ : Guard D Γ)
    (Body₂ : Cmd D Γ) :
    Cmd D (execSchema base Γ) :=
  .ite
    (phase₁Guard (D := D) base Γ)
    (phase₁Branch base G₁ Body₁ Close₁ Init₂)
    (phase₂Branch base G₂ Body₂)

/- Flatten two explicit framed-loop decompositions. -/
def commandOfParts
    (base : A)
    (Init₁ : Cmd D Γ)
    (G₁ : Guard D Γ)
    (Body₁ Close₁ : Cmd D Γ)
    (Init₂ : Cmd D Γ)
    (G₂ : Guard D Γ)
    (Body₂ Close₂ : Cmd D Γ) :
    Cmd D (execSchema base Γ) :=
  Cmd.framedLoopCommand
    (initBlock base Init₁)
    (loopGuard (D := D) base Γ)
    (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
    (liftCmd base Γ Close₂)

/- Program-level flattened two-loop command. -/
def programOfParts
    (base : A)
    (Init₁ : Cmd D Γ)
    (G₁ : Guard D Γ)
    (Body₁ Close₁ : Cmd D Γ)
    (Init₂ : Cmd D Γ)
    (G₂ : Guard D Γ)
    (Body₂ Close₂ : Cmd D Γ) :
    Program D Γ Γ where
  execSchema := execSchema base Γ
  extendsInput := execSchema_extension base Γ
  extendsOutput := execSchema_extension base Γ
  cmd :=
    commandOfParts
      base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂ Close₂

/- Flatten two commands when both are framed loops. -/
def flattenSeq?
    (base : A)
    (C₁ C₂ : Cmd D Γ) :
    Option (Program D Γ Γ) :=
  match C₁.framedLoopParts?, C₂.framedLoopParts? with
  | some (Init₁, G₁, Body₁, Close₁),
      some (Init₂, G₂, Body₂, Close₂) =>
      some
        (programOfParts
          base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
          Close₂)
  | _, _ =>
      none

/- Flatten only an unambiguous syntactic sequence. -/
def flattenCommand?
    (base : A)
    (C : Cmd D Γ) :
    Option (Program D Γ Γ) :=
  match C with
  | .seq C₁ C₂ => flattenSeq? base C₁ C₂
  | _ => none

end TwoLoopFlat

end Whiel

------------------------------------------------------------
-- Basic Construction Facts
------------------------------------------------------------

namespace Whiel

namespace TwoLoopFlat

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The lifted command has the same assigned names. -/
@[simp] theorem assignedSymbols_liftCmd
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ) :
    (liftCmd base Γ C).assignedSymbols =
      C.assignedSymbols := by
  simp [liftCmd]

/- The lifted command is loop-free iff the source is. -/
theorem loopFree_liftCmd
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ) :
    (liftCmd base Γ C).LoopFree ↔ C.LoopFree := by
  simp [liftCmd, Cmd.loopFree_onExtension,
    Cmd.loopFree_clean]

/- Phase-flag assignments are loop-free. -/
theorem loopFree_setPhase₁True
    (base : A)
    (Γ : UnnamedSchema A) :
    (setPhase₁True (D := D) base Γ).LoopFree := by
  simp [setPhase₁True, assignTrue, Cmd.LoopFree]

/- Phase-flag assignments are loop-free. -/
theorem loopFree_setPhase₁False
    (base : A)
    (Γ : UnnamedSchema A) :
    (setPhase₁False (D := D) base Γ).LoopFree := by
  simp [setPhase₁False, assignFalse, Cmd.LoopFree]

/- Phase-flag assignments are loop-free. -/
theorem loopFree_setPhase₂True
    (base : A)
    (Γ : UnnamedSchema A) :
    (setPhase₂True (D := D) base Γ).LoopFree := by
  simp [setPhase₂True, assignTrue, Cmd.LoopFree]

/- Phase-flag assignments are loop-free. -/
theorem loopFree_setPhase₂False
    (base : A)
    (Γ : UnnamedSchema A) :
    (setPhase₂False (D := D) base Γ).LoopFree := by
  simp [setPhase₂False, assignFalse, Cmd.LoopFree]

/- The flattened preamble is loop-free when the first
  source preamble is loop-free. -/
theorem loopFree_initBlock
    (base : A)
    {Init₁ : Cmd D Γ}
    (hInit₁ : Init₁.LoopFree) :
    (initBlock base Init₁).LoopFree := by
  rw [initBlock, Cmd.loopFree_seqList_iff]
  intro C hC
  simp only [List.mem_cons, List.not_mem_nil, or_false]
    at hC
  rcases hC with hC | hC | hC
  · subst hC
    exact (loopFree_liftCmd base Γ Init₁).mpr hInit₁
  · subst hC
    exact loopFree_setPhase₁True base Γ
  · subst hC
    exact loopFree_setPhase₂False base Γ

/- The first-loop exit branch is loop-free under source
  loop-freedom side conditions. -/
theorem loopFree_finishFirstBranch
    (base : A)
    {Close₁ Init₂ : Cmd D Γ}
    (hClose₁ : Close₁.LoopFree)
    (hInit₂ : Init₂.LoopFree) :
    (finishFirstBranch base Close₁ Init₂).LoopFree := by
  rw [finishFirstBranch, Cmd.loopFree_seqList_iff]
  intro C hC
  simp only [List.mem_cons, List.not_mem_nil, or_false]
    at hC
  rcases hC with hC | hC | hC | hC
  · subst hC
    exact (loopFree_liftCmd base Γ Close₁).mpr hClose₁
  · subst hC
    exact (loopFree_liftCmd base Γ Init₂).mpr hInit₂
  · subst hC
    exact loopFree_setPhase₁False base Γ
  · subst hC
    exact loopFree_setPhase₂True base Γ

/- The first dispatcher branch is loop-free. -/
theorem loopFree_phase₁Branch
    (base : A)
    (G₁ : Guard D Γ)
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    (hBody₁ : Body₁.LoopFree)
    (hClose₁ : Close₁.LoopFree)
    (hInit₂ : Init₂.LoopFree) :
    (phase₁Branch base G₁ Body₁ Close₁ Init₂).LoopFree := by
  exact Cmd.loopFree_ite
    (liftGuard base Γ G₁)
    ((loopFree_liftCmd base Γ Body₁).mpr hBody₁)
    (loopFree_finishFirstBranch base hClose₁ hInit₂)

/- The second dispatcher branch is loop-free. -/
theorem loopFree_phase₂Branch
    (base : A)
    (G₂ : Guard D Γ)
    {Body₂ : Cmd D Γ}
    (hBody₂ : Body₂.LoopFree) :
    (phase₂Branch base G₂ Body₂).LoopFree := by
  exact Cmd.loopFree_ite
    (liftGuard base Γ G₂)
    ((loopFree_liftCmd base Γ Body₂).mpr hBody₂)
    (loopFree_setPhase₂False base Γ)

/- The flattened dispatcher body is loop-free. -/
theorem loopFree_loopBody
    (base : A)
    (G₁ : Guard D Γ)
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    (hBody₁ : Body₁.LoopFree)
    (hClose₁ : Close₁.LoopFree)
    (hInit₂ : Init₂.LoopFree)
    (G₂ : Guard D Γ)
    {Body₂ : Cmd D Γ}
    (hBody₂ : Body₂.LoopFree) :
    Cmd.LoopFree
      (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂) := by
  exact Cmd.loopFree_ite
    (phase₁Guard (D := D) base Γ)
    (loopFree_phase₁Branch
      base G₁ hBody₁ hClose₁ hInit₂)
    (loopFree_phase₂Branch base G₂ hBody₂)

/- `flattenCommand?` delegates exactly on syntactic
  sequences. -/
@[simp] theorem flattenCommand?_seq
    (base : A)
    (C₁ C₂ : Cmd D Γ) :
    flattenCommand? base (.seq C₁ C₂) =
      flattenSeq? base C₁ C₂ :=
  rfl

/- Non-sequence commands are not accepted by
  `flattenCommand?`. -/
@[simp] theorem flattenCommand?_skip
    (base : A) :
    flattenCommand? base (.skip : Cmd D Γ) = none :=
  rfl

/- Non-sequence commands are not accepted by
  `flattenCommand?`. -/
@[simp] theorem flattenCommand?_assign
    (base : A)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    flattenCommand? base (.assign X e) = none :=
  rfl

/- Non-sequence commands are not accepted by
  `flattenCommand?`. -/
@[simp] theorem flattenCommand?_ite
    (base : A)
    (G : Guard D Γ)
    (C₁ C₂ : Cmd D Γ) :
    flattenCommand? base (.ite G C₁ C₂) = none :=
  rfl

/- Non-sequence commands are not accepted by
  `flattenCommand?`. -/
@[simp] theorem flattenCommand?_while
    (base : A)
    (G : Guard D Γ)
    (C : Cmd D Γ) :
    flattenCommand? base (.while G C) = none :=
  rfl

/- Successful framed-loop extraction on both inputs gives
  the expected flattened program. -/
theorem flattenSeq?_of_parts
    {base : A}
    {C₁ C₂ Init₁ Body₁ Close₁ Init₂ Body₂ Close₂ :
      Cmd D Γ}
    {G₁ G₂ : Guard D Γ}
    (h₁ :
      C₁.framedLoopParts? =
        some (Init₁, G₁, Body₁, Close₁))
    (h₂ :
      C₂.framedLoopParts? =
        some (Init₂, G₂, Body₂, Close₂)) :
    flattenSeq? base C₁ C₂ =
      some
        (programOfParts
          base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
          Close₂) := by
  simp [flattenSeq?, h₁, h₂]

------------------------------------------------------------
-- Semantic Support
------------------------------------------------------------

end TwoLoopFlat

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

variable {Ω : UnnamedSchema A}

/- Reduct compatibility for a retagged while loop. -/
private theorem onExtension_while_bigStep_reduct
    (hExt : Ω.extensionOf Γ)
    {G : Guard D Γ}
    {Body : Cmd D Γ}
    (hBody :
      ∀ {I J : Instance D Ω},
        BigStep (Body.onExtension hExt) I J →
          BigStep Body
            (Instance.reduct hExt I)
            (Instance.reduct hExt J))
    {I J : Instance D Ω} :
    BigStep
        (.while (G.onExtension hExt)
          (Body.onExtension hExt)) I J →
      BigStep (.while G Body)
        (Instance.reduct hExt I)
        (Instance.reduct hExt J) := by
  intro h
  generalize hW :
      (Whiel.Cmd.«while» (G.onExtension hExt)
        (Body.onExtension hExt) : Cmd D Ω) = W at h
  induction h generalizing G Body with
  | skip I =>
      cases hW
  | assign I X E =>
      cases hW
  | seq h₁ h₂ ih₁ ih₂ =>
      cases hW
  | ite_true hEval hStep ih =>
      cases hW
  | ite_false hEval hStep ih =>
      cases hW
  | while_false hFalse =>
      cases hW
      letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
      exact BigStep.while_false
        (fun hEval =>
          hFalse
            ((Guard.onExtension_eval_reduct
              (Γ := Ω) (Δ := Γ)
              G _ _ rfl).mpr
              hEval))
  | while_true hEval hBodyStep hLoop ihBodyStep ihLoop =>
      cases hW
      letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
      exact BigStep.while_true
        ((Guard.onExtension_eval_reduct
          (Γ := Ω) (Δ := Γ)
          G _ _ rfl).mp hEval)
        (hBody hBodyStep)
        (ihLoop hBody rfl)

/- Running a retagged command and then reducing gives a
  run of the original command. -/
theorem onExtension_bigStep_reduct
    (hExt : Ω.extensionOf Γ)
    {C : Cmd D Γ}
    {I J : Instance D Ω}
    (hStep : BigStep (C.onExtension hExt) I J) :
    BigStep C
      (Instance.reduct hExt I)
      (Instance.reduct hExt J) := by
  induction C generalizing I J with
  | skip =>
      have hEq :
          J = I := by
        exact (bigStep_skip_iff I J).mp
          (by simpa [onExtension] using hStep)
      rw [hEq]
      exact BigStep.skip (Instance.reduct hExt I)
  | assign X e =>
      have hAssign :
          J =
            Instance.update I
              (UnnamedSchema.symOfExtension hExt X)
              ((RAExpr.castArity
                (UnnamedSchema.arity_eq_of_extensionOf
                  hExt X)
                (e.onExtension hExt)).eval I) := by
        exact
          (bigStep_assign_iff I J
            (UnnamedSchema.symOfExtension hExt X)
            (RAExpr.castArity
              (UnnamedSchema.arity_eq_of_extensionOf
                hExt X)
              (e.onExtension hExt))).mp
            (by simpa [onExtension] using hStep)
      rw [hAssign]
      rw [bigStep_assign_iff]
      rw [Instance.reduct_update_of_mem]
      let hAr :=
        UnnamedSchema.arity_eq_of_extensionOf hExt X
      have hEval :
          cast
              (congrArg (FinRelation D) hAr)
              ((RAExpr.castArity hAr
                (e.onExtension hExt)).eval I) =
            e.eval (Instance.reduct hExt I) := by
        letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
        rw [RAExpr.cast_eval_castArity]
        exact RAExpr.reduct_property (Δ := Ω) (e := e) I
      rw [hEval]
  | seq C₁ C₂ ih₁ ih₂ =>
      have hSeq :
          ∃ K : Instance D Ω,
            BigStep (C₁.onExtension hExt) I K ∧
              BigStep (C₂.onExtension hExt) K J := by
        exact
          (bigStep_seq_iff
            (C₁.onExtension hExt)
            (C₂.onExtension hExt) I J).mp
            (by simpa [onExtension] using hStep)
      rcases hSeq with ⟨K, h₁, h₂⟩
      exact BigStep.seq (ih₁ h₁) (ih₂ h₂)
  | ite G C₁ C₂ ih₁ ih₂ =>
      have hIte :
          (G.onExtension hExt).eval I ∧
              BigStep (C₁.onExtension hExt) I J ∨
            ¬ (G.onExtension hExt).eval I ∧
              BigStep (C₂.onExtension hExt) I J := by
        exact
          (bigStep_ite_iff
            (G.onExtension hExt)
            (C₁.onExtension hExt)
            (C₂.onExtension hExt) I J).mp
            (by simpa [onExtension] using hStep)
      letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
      cases hIte with
      | inl h =>
          have hG :
              G.eval (Instance.reduct hExt I) :=
            (Guard.onExtension_eval_reduct
              (Γ := Ω) (Δ := Γ)
              G I (Instance.reduct hExt I) rfl).mp h.1
          exact BigStep.ite_true hG (ih₁ h.2)
      | inr h =>
          have hG :
              ¬ G.eval (Instance.reduct hExt I) := by
            intro hEval
            exact h.1
              ((Guard.onExtension_eval_reduct
                (Γ := Ω) (Δ := Γ)
                G I (Instance.reduct hExt I) rfl).mpr
                hEval)
          exact BigStep.ite_false hG (ih₂ h.2)
  | «while» G Body ihBody =>
      exact onExtension_while_bigStep_reduct
        hExt (fun h => ihBody h) hStep

/- Original command runs lift to retagged command runs. -/
theorem onExtension_bigStep_lift
    (hExt : Ω.extensionOf Γ)
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    {IΩ : Instance D Ω}
    (hReduct : Instance.reduct hExt IΩ = I)
    (hStep : BigStep C I J) :
    ∃ JΩ : Instance D Ω,
      BigStep (C.onExtension hExt) IΩ JΩ ∧
        Instance.reduct hExt JΩ = J := by
  induction hStep generalizing IΩ with
  | skip I =>
      refine ⟨IΩ, ?_, hReduct⟩
      exact BigStep.skip IΩ
  | assign I X e =>
      let XΩ := UnnamedSchema.symOfExtension hExt X
      let hAr := UnnamedSchema.arity_eq_of_extensionOf hExt X
      let eΩ :=
        RAExpr.castArity hAr (e.onExtension hExt)
      refine
        ⟨Instance.update IΩ XΩ (eΩ.eval IΩ), ?_, ?_⟩
      · exact BigStep.assign IΩ XΩ eΩ
      · rw [Instance.reduct_update_of_mem]
        rw [hReduct]
        have hEval :
            cast (congrArg (FinRelation D) hAr)
                (eΩ.eval IΩ) =
              e.eval I := by
          letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
          rw [RAExpr.cast_eval_castArity]
          simpa [hReduct] using
            (RAExpr.reduct_property
              (Δ := Ω) (e := e) IΩ)
        rw [hEval]
  | seq h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ hReduct with ⟨KΩ, hKStep, hKReduct⟩
      rcases ih₂ hKReduct with ⟨JΩ, hJStep, hJReduct⟩
      refine ⟨JΩ, ?_, hJReduct⟩
      exact BigStep.seq hKStep hJStep
  | ite_true hG hC ih =>
      rcases ih hReduct with ⟨JΩ, hStepΩ, hJReduct⟩
      refine ⟨JΩ, ?_, hJReduct⟩
      letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
      exact BigStep.ite_true
        ((Guard.onExtension_eval_reduct
          (Γ := Ω) (Δ := Γ)
          _ _ _ hReduct).mpr hG)
        hStepΩ
  | ite_false hG hC ih =>
      rcases ih hReduct with ⟨JΩ, hStepΩ, hJReduct⟩
      refine ⟨JΩ, ?_, hJReduct⟩
      letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
      exact BigStep.ite_false
        (fun hEval =>
          hG
            ((Guard.onExtension_eval_reduct
              (Γ := Ω) (Δ := Γ)
              _ _ _ hReduct).mp hEval))
        hStepΩ
  | while_false hG =>
      refine ⟨IΩ, ?_, hReduct⟩
      letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
      exact BigStep.while_false
        (fun hEval =>
          hG
            ((Guard.onExtension_eval_reduct
              (Γ := Ω) (Δ := Γ)
              _ _ _ hReduct).mp hEval))
  | while_true hG hBody hLoop ihBody ihLoop =>
      rcases ihBody hReduct with
        ⟨KΩ, hBodyΩ, hKReduct⟩
      rcases ihLoop hKReduct with
        ⟨JΩ, hLoopΩ, hJReduct⟩
      refine ⟨JΩ, ?_, hJReduct⟩
      letI : Fact (Ω.extensionOf Γ) := ⟨hExt⟩
      exact BigStep.while_true
        ((Guard.onExtension_eval_reduct
          (Γ := Ω) (Δ := Γ)
          _ _ _ hReduct).mpr hG)
        hBodyΩ
        hLoopΩ

end Cmd

namespace TwoLoopFlat

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The first phase flag is hidden from the source schema. -/
theorem phase₁Sym_not_mem
    (base : A)
    (Γ : UnnamedSchema A) :
    (phase₁Sym base Γ).1 ∉ Γ.syms := by
  simpa [phase₁Sym, phase₁Name,
    UnnamedSchema.symOfExtension] using
    phase₁_fresh base Γ

/- The second phase flag is hidden from the source schema. -/
theorem phase₂Sym_not_mem
    (base : A)
    (Γ : UnnamedSchema A) :
    (phase₂Sym base Γ).1 ∉ Γ.syms := by
  simpa [phase₂Sym, phase₂Name, phase₁Schema,
    UnnamedSchema.insertedSym,
    UnnamedSchema.insertFresh] using
    phase₂_fresh base Γ

/- The first phase flag is not assigned by lifted source
  commands. -/
theorem phase₁_not_assigned_liftCmd
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ) :
    (phase₁Sym base Γ).1 ∉
      (liftCmd (D := D) base Γ C).assignedSymbols := by
  rw [assignedSymbols_liftCmd]
  intro hMem
  exact phase₁Sym_not_mem base Γ
    (Cmd.assignedSymbols_subset_syms C hMem)

/- The second phase flag is not assigned by lifted source
  commands. -/
theorem phase₂_not_assigned_liftCmd
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ) :
    (phase₂Sym base Γ).1 ∉
      (liftCmd (D := D) base Γ C).assignedSymbols := by
  rw [assignedSymbols_liftCmd]
  intro hMem
  exact phase₂Sym_not_mem base Γ
    (Cmd.assignedSymbols_subset_syms C hMem)

/- Phase one: source reduct agrees with `I`, `p₁` is
  true, and `p₂` is false. -/
def Phase₁
    (base : A)
    (J : Instance D (execSchema base Γ))
    (I : Instance D Γ) : Prop :=
  Instance.reduct (execSchema_extension base Γ) J = I ∧
    (phase₁Guard (D := D) base Γ).eval J ∧
      ¬ (phase₂Guard (D := D) base Γ).eval J

/- Phase two: source reduct agrees with `I`, `p₁` is
  false, and `p₂` is true. -/
def Phase₂
    (base : A)
    (J : Instance D (execSchema base Γ))
    (I : Instance D Γ) : Prop :=
  Instance.reduct (execSchema_extension base Γ) J = I ∧
    ¬ (phase₁Guard (D := D) base Γ).eval J ∧
      (phase₂Guard (D := D) base Γ).eval J

/- Done phase: source reduct agrees with `I`, and both
  phase flags are false. -/
def Done
    (base : A)
    (J : Instance D (execSchema base Γ))
    (I : Instance D Γ) : Prop :=
  Instance.reduct (execSchema_extension base Γ) J = I ∧
    ¬ (phase₁Guard (D := D) base Γ).eval J ∧
      ¬ (phase₂Guard (D := D) base Γ).eval J

/- Setting phase one preserves the source reduct. -/
theorem setPhase₁True_reduct
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₁True (D := D) base Γ) J J') :
    Instance.reduct (execSchema_extension base Γ) J' =
      Instance.reduct (execSchema_extension base Γ) J := by
  rw [setPhase₁True, assignTrue,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  exact Instance.reduct_update_of_not_mem
    (execSchema_extension base Γ) J
    (phase₁Sym base Γ) _ (phase₁Sym_not_mem base Γ)

/- Clearing phase one preserves the source reduct. -/
theorem setPhase₁False_reduct
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₁False (D := D) base Γ) J J') :
    Instance.reduct (execSchema_extension base Γ) J' =
      Instance.reduct (execSchema_extension base Γ) J := by
  rw [setPhase₁False, assignFalse,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  exact Instance.reduct_update_of_not_mem
    (execSchema_extension base Γ) J
    (phase₁Sym base Γ) _ (phase₁Sym_not_mem base Γ)

/- Setting phase two preserves the source reduct. -/
theorem setPhase₂True_reduct
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₂True (D := D) base Γ) J J') :
    Instance.reduct (execSchema_extension base Γ) J' =
      Instance.reduct (execSchema_extension base Γ) J := by
  rw [setPhase₂True, assignTrue,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  exact Instance.reduct_update_of_not_mem
    (execSchema_extension base Γ) J
    (phase₂Sym base Γ) _ (phase₂Sym_not_mem base Γ)

/- Clearing phase two preserves the source reduct. -/
theorem setPhase₂False_reduct
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₂False (D := D) base Γ) J J') :
    Instance.reduct (execSchema_extension base Γ) J' =
      Instance.reduct (execSchema_extension base Γ) J := by
  rw [setPhase₂False, assignFalse,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  exact Instance.reduct_update_of_not_mem
    (execSchema_extension base Γ) J
    (phase₂Sym base Γ) _ (phase₂Sym_not_mem base Γ)

/- Setting phase one makes its guard true. -/
theorem setPhase₁True_phase₁
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₁True (D := D) base Γ) J J') :
    (phase₁Guard (D := D) base Γ).eval J' := by
  rw [setPhase₁True, assignTrue,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  unfold phase₁Guard flagGuard
  rw [Guard.eval, eval_rel, Instance.update_lookup_eq]
  rw [trueExpr_eval, trueExpr_eval]

/- Clearing phase one makes its guard false. -/
theorem setPhase₁False_not_phase₁
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₁False (D := D) base Γ) J J') :
    ¬ (phase₁Guard (D := D) base Γ).eval J' := by
  rw [setPhase₁False, assignFalse,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  unfold phase₁Guard flagGuard
  rw [Guard.eval, eval_rel, Instance.update_lookup_eq]
  exact falseExpr_eval_ne_trueExpr_eval
    (phase₁Sym base Γ) (phase₁_arity base Γ) J _

/- Setting phase two makes its guard true. -/
theorem setPhase₂True_phase₂
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₂True (D := D) base Γ) J J') :
    (phase₂Guard (D := D) base Γ).eval J' := by
  rw [setPhase₂True, assignTrue,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  unfold phase₂Guard flagGuard
  rw [Guard.eval, eval_rel, Instance.update_lookup_eq]
  rw [trueExpr_eval, trueExpr_eval]

/- Clearing phase two makes its guard false. -/
theorem setPhase₂False_not_phase₂
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₂False (D := D) base Γ) J J') :
    ¬ (phase₂Guard (D := D) base Γ).eval J' := by
  rw [setPhase₂False, assignFalse,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  unfold phase₂Guard flagGuard
  rw [Guard.eval, eval_rel, Instance.update_lookup_eq]
  exact falseExpr_eval_ne_trueExpr_eval
    (phase₂Sym base Γ) (phase₂_arity base Γ) J _

/- Updating phase two to false preserves the phase-one
  guard. -/
theorem setPhase₂False_preserves_phase₁
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₂False (D := D) base Γ) J J')
    (hPhase₁ :
      (phase₁Guard (D := D) base Γ).eval J) :
    (phase₁Guard (D := D) base Γ).eval J' := by
  rw [setPhase₂False, assignFalse,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  unfold phase₁Guard flagGuard at hPhase₁ ⊢
  rw [Guard.eval, eval_rel] at hPhase₁
  rw [Guard.eval, eval_rel,
    Instance.update_lookup_ne]
  · exact hPhase₁
  · exact phase₁Sym_ne_phase₂Sym base Γ

/- Updating phase two to true preserves phase-one falsity. -/
theorem setPhase₂True_preserves_not_phase₁
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₂True (D := D) base Γ) J J')
    (hNotPhase₁ :
      ¬ (phase₁Guard (D := D) base Γ).eval J) :
    ¬ (phase₁Guard (D := D) base Γ).eval J' := by
  rw [setPhase₂True, assignTrue,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  intro hPhase₁
  apply hNotPhase₁
  unfold phase₁Guard flagGuard at hPhase₁ ⊢
  rw [Guard.eval, eval_rel] at hPhase₁
  rw [Instance.update_lookup_ne] at hPhase₁
  · rw [Guard.eval, eval_rel]
    rw [trueExpr_eval] at hPhase₁
    rw [trueExpr_eval]
    exact hPhase₁
  · exact phase₁Sym_ne_phase₂Sym base Γ

/- Updating phase two to false preserves phase-one falsity. -/
theorem setPhase₂False_preserves_not_phase₁
    (base : A)
    (Γ : UnnamedSchema A)
    {J J' : Instance D (execSchema base Γ)}
    (hStep :
      Cmd.BigStep (setPhase₂False (D := D) base Γ) J J')
    (hNotPhase₁ :
      ¬ (phase₁Guard (D := D) base Γ).eval J) :
    ¬ (phase₁Guard (D := D) base Γ).eval J' := by
  rw [setPhase₂False, assignFalse,
    Cmd.bigStep_assign_iff] at hStep
  subst hStep
  intro hPhase₁
  apply hNotPhase₁
  unfold phase₁Guard flagGuard at hPhase₁ ⊢
  rw [Guard.eval, eval_rel] at hPhase₁
  rw [Instance.update_lookup_ne] at hPhase₁
  · rw [Guard.eval, eval_rel]
    rw [trueExpr_eval] at hPhase₁
    rw [trueExpr_eval]
    exact hPhase₁
  · exact phase₁Sym_ne_phase₂Sym base Γ

/- Lifted command runs reduce to cleaned source runs. -/
theorem liftCmd_bigStep_reduct
    (base : A)
    (Γ : UnnamedSchema A)
    {C : Cmd D Γ}
    {I J : Instance D (execSchema base Γ)}
    (hStep : Cmd.BigStep (liftCmd base Γ C) I J) :
    Cmd.BigStep C
      (Instance.reduct (execSchema_extension base Γ) I)
      (Instance.reduct (execSchema_extension base Γ) J) := by
  have hClean :
      Cmd.BigStep C.clean
        (Instance.reduct (execSchema_extension base Γ) I)
        (Instance.reduct (execSchema_extension base Γ) J) :=
    Cmd.onExtension_bigStep_reduct
      (execSchema_extension base Γ)
      (by simpa [liftCmd] using hStep)
  exact
    (Cmd.bigStep_clean_iff C
      (Instance.reduct (execSchema_extension base Γ) I)
      (Instance.reduct (execSchema_extension base Γ) J)).mp
      hClean

/- Source command runs lift to cleaned retagged command
  runs. -/
theorem liftCmd_bigStep_lift
    (base : A)
    (Γ : UnnamedSchema A)
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hReduct :
      Instance.reduct (execSchema_extension base Γ) IΩ =
        I)
    (hStep : Cmd.BigStep C I J) :
    ∃ JΩ : Instance D (execSchema base Γ),
      Cmd.BigStep (liftCmd base Γ C) IΩ JΩ ∧
        Instance.reduct (execSchema_extension base Γ) JΩ =
          J := by
  have hClean :
      Cmd.BigStep C.clean I J :=
    (Cmd.bigStep_clean_iff C I J).mpr hStep
  rcases
    Cmd.onExtension_bigStep_lift
      (execSchema_extension base Γ)
      hReduct
      hClean
    with ⟨JΩ, hLift, hReductJ⟩
  exact ⟨JΩ, by simpa [liftCmd] using hLift, hReductJ⟩

/- Lifted guard evaluation agrees with source guard
  evaluation on the reduct. -/
theorem liftGuard_eval_iff
    (base : A)
    (Γ : UnnamedSchema A)
    (G : Guard D Γ)
    (J : Instance D (execSchema base Γ)) :
    (liftGuard (D := D) base Γ G).eval J ↔
      G.eval
        (Instance.reduct (execSchema_extension base Γ) J) := by
  letI : Fact ((execSchema base Γ).extensionOf Γ) :=
    ⟨execSchema_extension base Γ⟩
  unfold liftGuard
  exact
    Iff.trans
      (Guard.onExtension_eval_reduct
        (Γ := execSchema base Γ) (Δ := Γ)
        G.clean J
        (Instance.reduct (execSchema_extension base Γ) J)
        rfl)
      (Guard.eval_clean_iff
        (Instance.reduct (execSchema_extension base Γ) J)
        G)

/- The dispatcher guard is exactly the disjunction of the
  two phase guards. -/
theorem loopGuard_eval_iff
    (base : A)
    (Γ : UnnamedSchema A)
    (J : Instance D (execSchema base Γ)) :
    (loopGuard (D := D) base Γ).eval J ↔
      (phase₁Guard (D := D) base Γ).eval J ∨
        (phase₂Guard (D := D) base Γ).eval J := by
  unfold loopGuard
  simpa [Guard.eval] using
    (Guard.eval_cleanOr_iff
      (I := J)
      (phase₁Guard (D := D) base Γ)
      (phase₂Guard (D := D) base Γ))

/- Phase one makes the dispatcher guard true. -/
theorem Phase₁_loopGuard
    (base : A)
    {J : Instance D (execSchema base Γ)}
    {I : Instance D Γ}
    (hPhase : Phase₁ (D := D) base J I) :
    (loopGuard (D := D) base Γ).eval J :=
  (loopGuard_eval_iff (D := D) base Γ J).mpr
    (Or.inl hPhase.2.1)

/- Phase two makes the dispatcher guard true. -/
theorem Phase₂_loopGuard
    (base : A)
    {J : Instance D (execSchema base Γ)}
    {I : Instance D Γ}
    (hPhase : Phase₂ (D := D) base J I) :
    (loopGuard (D := D) base Γ).eval J :=
  (loopGuard_eval_iff (D := D) base Γ J).mpr
    (Or.inr hPhase.2.2)

/- Done makes the dispatcher guard false. -/
theorem Done_not_loopGuard
    (base : A)
    {J : Instance D (execSchema base Γ)}
    {I : Instance D Γ}
    (hDone : Done (D := D) base J I) :
    ¬ (loopGuard (D := D) base Γ).eval J := by
  intro hGuard
  cases (loopGuard_eval_iff (D := D) base Γ J).mp
      hGuard with
  | inl hPhase₁ => exact hDone.2.1 hPhase₁
  | inr hPhase₂ => exact hDone.2.2 hPhase₂

/- Lifted source commands preserve the first phase guard. -/
theorem liftCmd_preserves_phase₁Guard
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ)
    {J J' : Instance D (execSchema base Γ)}
    (hStep : Cmd.BigStep (liftCmd (D := D) base Γ C) J J') :
    (phase₁Guard (D := D) base Γ).eval J' ↔
      (phase₁Guard (D := D) base Γ).eval J := by
  have hRel :
      J' (phase₁Sym base Γ) = J (phase₁Sym base Γ) :=
    Cmd.BigStep.no_update_preservation
      hStep (phase₁Sym base Γ)
      (phase₁_not_assigned_liftCmd
        (D := D) base Γ C)
  constructor
  · intro h
    unfold phase₁Guard flagGuard at h ⊢
    rw [Guard.eval, eval_rel] at h
    rw [Guard.eval, eval_rel]
    rw [trueExpr_eval] at h ⊢
    rwa [hRel] at h
  · intro h
    unfold phase₁Guard flagGuard at h ⊢
    rw [Guard.eval, eval_rel] at h
    rw [Guard.eval, eval_rel]
    rw [trueExpr_eval] at h ⊢
    rwa [hRel]

/- Lifted source commands preserve the second phase guard. -/
theorem liftCmd_preserves_phase₂Guard
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ)
    {J J' : Instance D (execSchema base Γ)}
    (hStep : Cmd.BigStep (liftCmd (D := D) base Γ C) J J') :
    (phase₂Guard (D := D) base Γ).eval J' ↔
      (phase₂Guard (D := D) base Γ).eval J := by
  have hRel :
      J' (phase₂Sym base Γ) = J (phase₂Sym base Γ) :=
    Cmd.BigStep.no_update_preservation
      hStep (phase₂Sym base Γ)
      (phase₂_not_assigned_liftCmd
        (D := D) base Γ C)
  constructor
  · intro h
    unfold phase₂Guard flagGuard at h ⊢
    rw [Guard.eval, eval_rel] at h
    rw [Guard.eval, eval_rel]
    rw [trueExpr_eval] at h ⊢
    rwa [hRel] at h
  · intro h
    unfold phase₂Guard flagGuard at h ⊢
    rw [Guard.eval, eval_rel] at h
    rw [Guard.eval, eval_rel]
    rw [trueExpr_eval] at h ⊢
    rwa [hRel]

/- Initialization moves the flattened command to phase one. -/
theorem initBlock_bigStep_phase₁
    (base : A)
    {Init₁ : Cmd D Γ}
    {I J : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hReduct :
      Instance.reduct (execSchema_extension base Γ) IΩ =
        I)
    (hInit : Cmd.BigStep Init₁ I J) :
    ∃ JΩ : Instance D (execSchema base Γ),
      Cmd.BigStep (initBlock base Init₁) IΩ JΩ ∧
        Phase₁ (D := D) base JΩ J := by
  rcases
    liftCmd_bigStep_lift
      (D := D) base Γ hReduct hInit with
    ⟨J1Ω, hInitΩ, hJ1Reduct⟩
  let J2Ω : Instance D (execSchema base Γ) :=
    Instance.update J1Ω (phase₁Sym base Γ)
      ((trueExpr (D := D)
        (phase₁Sym base Γ) (phase₁_arity base Γ)).eval J1Ω)
  have hSet1 :
      Cmd.BigStep (setPhase₁True (D := D) base Γ)
        J1Ω J2Ω := by
    simp [J2Ω, setPhase₁True, assignTrue]
  let J3Ω : Instance D (execSchema base Γ) :=
    Instance.update J2Ω (phase₂Sym base Γ)
      ((falseExpr (D := D)
        (phase₂Sym base Γ) (phase₂_arity base Γ)).eval J2Ω)
  have hSet2 :
      Cmd.BigStep (setPhase₂False (D := D) base Γ)
        J2Ω J3Ω := by
    simp [J3Ω, setPhase₂False, assignFalse]
  refine ⟨J3Ω, ?_, ?_⟩
  · simpa [initBlock, Cmd.seqList] using
      (Cmd.BigStep.seq hInitΩ
        (Cmd.BigStep.seq hSet1
          (Cmd.BigStep.seq hSet2
            (Cmd.BigStep.skip J3Ω))))
  · unfold Phase₁
    refine ⟨?_, ?_, ?_⟩
    · calc
        Instance.reduct (execSchema_extension base Γ) J3Ω =
            Instance.reduct (execSchema_extension base Γ) J2Ω :=
          setPhase₂False_reduct
            (D := D) base Γ hSet2
        _ = Instance.reduct (execSchema_extension base Γ) J1Ω :=
          setPhase₁True_reduct
            (D := D) base Γ hSet1
        _ = J := hJ1Reduct
    · exact setPhase₂False_preserves_phase₁
        (D := D) base Γ hSet2
        (setPhase₁True_phase₁
          (D := D) base Γ hSet1)
    · exact setPhase₂False_not_phase₂
        (D := D) base Γ hSet2

/- Reverse initialization block runs to a source
  initialization run and phase one. -/
theorem initBlock_bigStep_phase₁_reverse
    (base : A)
    {Init₁ : Cmd D Γ}
    {I : Instance D Γ}
    {IΩ JΩ : Instance D (execSchema base Γ)}
    (hReduct :
      Instance.reduct (execSchema_extension base Γ) IΩ =
        I)
    (hStep : Cmd.BigStep (initBlock base Init₁) IΩ JΩ) :
    ∃ J : Instance D Γ,
      Cmd.BigStep Init₁ I J ∧
        Phase₁ (D := D) base JΩ J := by
  have hSeq :
      Cmd.BigStep
        (Cmd.seqList
          [ liftCmd base Γ Init₁,
            setPhase₁True (D := D) base Γ,
            setPhase₂False (D := D) base Γ ])
        IΩ JΩ := by
    simpa [initBlock] using hStep
  rw [Cmd.seqList, Cmd.bigStep_seq_iff] at hSeq
  rcases hSeq with ⟨J1Ω, hInitΩ, hRest₁⟩
  change
    Cmd.BigStep
      (.seq (setPhase₁True (D := D) base Γ)
        (Cmd.seqList [setPhase₂False (D := D) base Γ]))
      J1Ω JΩ at hRest₁
  rw [Cmd.bigStep_seq_iff] at hRest₁
  rcases hRest₁ with ⟨J2Ω, hSet1, hRest₂⟩
  change
    Cmd.BigStep
      (.seq (setPhase₂False (D := D) base Γ)
        (Cmd.seqList ([] : List (Cmd D (execSchema base Γ)))))
      J2Ω JΩ at hRest₂
  rw [Cmd.bigStep_seq_iff] at hRest₂
  rcases hRest₂ with ⟨J3Ω, hSet2, hSkip⟩
  have hJΩ : JΩ = J3Ω :=
    (Cmd.bigStep_skip_iff J3Ω JΩ).mp
      (by simpa [Cmd.seqList] using hSkip)
  let J : Instance D Γ :=
    Instance.reduct (execSchema_extension base Γ) J1Ω
  have hInitSrc :
      Cmd.BigStep Init₁ I J := by
    simpa [J, hReduct] using
      (liftCmd_bigStep_reduct
        (D := D) base Γ hInitΩ)
  have hPhase :
      Phase₁ (D := D) base JΩ J := by
    rw [hJΩ]
    unfold Phase₁
    refine ⟨?_, ?_, ?_⟩
    · calc
        Instance.reduct (execSchema_extension base Γ) J3Ω =
            Instance.reduct (execSchema_extension base Γ) J2Ω :=
          setPhase₂False_reduct
            (D := D) base Γ hSet2
        _ = Instance.reduct (execSchema_extension base Γ) J1Ω :=
          setPhase₁True_reduct
            (D := D) base Γ hSet1
        _ = J := rfl
    · exact setPhase₂False_preserves_phase₁
        (D := D) base Γ hSet2
        (setPhase₁True_phase₁
          (D := D) base Γ hSet1)
    · exact setPhase₂False_not_phase₂
        (D := D) base Γ hSet2
  exact ⟨J, hInitSrc, hPhase⟩

/- Finishing loop one moves the flattened command to phase
  two. -/
theorem finishFirstBranch_bigStep_phase₂
    (base : A)
    {Close₁ Init₂ : Cmd D Γ}
    {I J K : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₁ (D := D) base IΩ I)
    (hClose : Cmd.BigStep Close₁ I J)
    (hInit₂ : Cmd.BigStep Init₂ J K) :
    ∃ KΩ : Instance D (execSchema base Γ),
      Cmd.BigStep (finishFirstBranch base Close₁ Init₂)
        IΩ KΩ ∧
        Phase₂ (D := D) base KΩ K := by
  rcases
    liftCmd_bigStep_lift
      (D := D) base Γ hPhase.1 hClose with
    ⟨JΩ, hCloseΩ, hJReduct⟩
  rcases
    liftCmd_bigStep_lift
      (D := D) base Γ hJReduct hInit₂ with
    ⟨K1Ω, hInitΩ, hK1Reduct⟩
  let K2Ω : Instance D (execSchema base Γ) :=
    Instance.update K1Ω (phase₁Sym base Γ)
      ((falseExpr (D := D)
        (phase₁Sym base Γ) (phase₁_arity base Γ)).eval K1Ω)
  have hSet1 :
      Cmd.BigStep (setPhase₁False (D := D) base Γ)
        K1Ω K2Ω := by
    simp [K2Ω, setPhase₁False, assignFalse]
  let K3Ω : Instance D (execSchema base Γ) :=
    Instance.update K2Ω (phase₂Sym base Γ)
      ((trueExpr (D := D)
        (phase₂Sym base Γ) (phase₂_arity base Γ)).eval K2Ω)
  have hSet2 :
      Cmd.BigStep (setPhase₂True (D := D) base Γ)
        K2Ω K3Ω := by
    simp [K3Ω, setPhase₂True, assignTrue]
  refine ⟨K3Ω, ?_, ?_⟩
  · simpa [finishFirstBranch, Cmd.seqList] using
      (Cmd.BigStep.seq hCloseΩ
        (Cmd.BigStep.seq hInitΩ
          (Cmd.BigStep.seq hSet1
            (Cmd.BigStep.seq hSet2
              (Cmd.BigStep.skip K3Ω)))))
  · unfold Phase₂
    refine ⟨?_, ?_, ?_⟩
    · calc
        Instance.reduct (execSchema_extension base Γ) K3Ω =
            Instance.reduct (execSchema_extension base Γ) K2Ω :=
          setPhase₂True_reduct
            (D := D) base Γ hSet2
        _ = Instance.reduct (execSchema_extension base Γ) K1Ω :=
          setPhase₁False_reduct
            (D := D) base Γ hSet1
        _ = K := hK1Reduct
    · exact setPhase₂True_preserves_not_phase₁
        (D := D) base Γ hSet2
        (setPhase₁False_not_phase₁
          (D := D) base Γ hSet1)
    · exact setPhase₂True_phase₂
        (D := D) base Γ hSet2

/- One dispatcher body step in phase one simulates one
  first-loop body step. -/
theorem loopBody_phase₁_body_forward
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I J : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₁ (D := D) base IΩ I)
    (hG : G₁.eval I)
    (hBody : Cmd.BigStep Body₁ I J) :
    ∃ JΩ : Instance D (execSchema base Γ),
      Cmd.BigStep
        (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
        IΩ JΩ ∧
        Phase₁ (D := D) base JΩ J := by
  rcases
    liftCmd_bigStep_lift
      (D := D) base Γ hPhase.1 hBody with
    ⟨JΩ, hBodyΩ, hJReduct⟩
  have hLiftG :
      (liftGuard (D := D) base Γ G₁).eval IΩ := by
    exact
      (liftGuard_eval_iff (D := D) base Γ G₁ IΩ).mpr
        (by simpa [hPhase.1] using hG)
  refine ⟨JΩ, ?_, ?_⟩
  · simpa [loopBody, phase₁Branch] using
      (Cmd.BigStep.ite_true hPhase.2.1
        (Cmd.BigStep.ite_true hLiftG hBodyΩ))
  · unfold Phase₁
    refine ⟨hJReduct, ?_, ?_⟩
    · exact
        (liftCmd_preserves_phase₁Guard
          (D := D) base Γ Body₁ hBodyΩ).mpr
          hPhase.2.1
    · intro hPhase₂
      exact hPhase.2.2
        ((liftCmd_preserves_phase₂Guard
          (D := D) base Γ Body₁ hBodyΩ).mp
          hPhase₂)

/- One dispatcher body step in phase one exits the first
  loop and enters phase two when `G₁` is false. -/
theorem loopBody_phase₁_exit_forward
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I J K : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₁ (D := D) base IΩ I)
    (hG : ¬ G₁.eval I)
    (hClose : Cmd.BigStep Close₁ I J)
    (hInit₂ : Cmd.BigStep Init₂ J K) :
    ∃ KΩ : Instance D (execSchema base Γ),
      Cmd.BigStep
        (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
        IΩ KΩ ∧
        Phase₂ (D := D) base KΩ K := by
  rcases
    finishFirstBranch_bigStep_phase₂
      (D := D) base hPhase hClose hInit₂ with
    ⟨KΩ, hFinish, hKPhase⟩
  have hLiftG :
      ¬ (liftGuard (D := D) base Γ G₁).eval IΩ := by
    intro hEval
    exact hG
      (by
        have hSrc :=
          (liftGuard_eval_iff
            (D := D) base Γ G₁ IΩ).mp hEval
        simpa [hPhase.1] using hSrc)
  refine ⟨KΩ, ?_, hKPhase⟩
  simpa [loopBody, phase₁Branch] using
    (Cmd.BigStep.ite_true hPhase.2.1
      (Cmd.BigStep.ite_false hLiftG hFinish))

/- One dispatcher body step in phase two simulates one
  second-loop body step. -/
theorem loopBody_phase₂_body_forward
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I J : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₂ (D := D) base IΩ I)
    (hG : G₂.eval I)
    (hBody : Cmd.BigStep Body₂ I J) :
    ∃ JΩ : Instance D (execSchema base Γ),
      Cmd.BigStep
        (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
        IΩ JΩ ∧
        Phase₂ (D := D) base JΩ J := by
  rcases
    liftCmd_bigStep_lift
      (D := D) base Γ hPhase.1 hBody with
    ⟨JΩ, hBodyΩ, hJReduct⟩
  have hLiftG :
      (liftGuard (D := D) base Γ G₂).eval IΩ := by
    exact
      (liftGuard_eval_iff (D := D) base Γ G₂ IΩ).mpr
        (by simpa [hPhase.1] using hG)
  refine ⟨JΩ, ?_, ?_⟩
  · simpa [loopBody, phase₂Branch] using
      (Cmd.BigStep.ite_false hPhase.2.1
        (Cmd.BigStep.ite_true hLiftG hBodyΩ))
  · unfold Phase₂
    refine ⟨hJReduct, ?_, ?_⟩
    · intro hPhase₁
      exact hPhase.2.1
        ((liftCmd_preserves_phase₁Guard
          (D := D) base Γ Body₂ hBodyΩ).mp
          hPhase₁)
    · exact
        (liftCmd_preserves_phase₂Guard
          (D := D) base Γ Body₂ hBodyΩ).mpr
          hPhase.2.2

/- One dispatcher body step in phase two exits the second
  loop and reaches `Done` when `G₂` is false. -/
theorem loopBody_phase₂_exit_forward
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₂ (D := D) base IΩ I)
    (hG : ¬ G₂.eval I) :
    ∃ JΩ : Instance D (execSchema base Γ),
      Cmd.BigStep
        (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
        IΩ JΩ ∧
        Done (D := D) base JΩ I := by
  let JΩ : Instance D (execSchema base Γ) :=
    Instance.update IΩ (phase₂Sym base Γ)
      ((falseExpr (D := D)
        (phase₂Sym base Γ) (phase₂_arity base Γ)).eval IΩ)
  have hSet :
      Cmd.BigStep (setPhase₂False (D := D) base Γ)
        IΩ JΩ := by
    simp [JΩ, setPhase₂False, assignFalse]
  have hLiftG :
      ¬ (liftGuard (D := D) base Γ G₂).eval IΩ := by
    intro hEval
    exact hG
      (by
        have hSrc :=
          (liftGuard_eval_iff
            (D := D) base Γ G₂ IΩ).mp hEval
        simpa [hPhase.1] using hSrc)
  refine ⟨JΩ, ?_, ?_⟩
  · simpa [loopBody, phase₂Branch] using
      (Cmd.BigStep.ite_false hPhase.2.1
        (Cmd.BigStep.ite_false hLiftG hSet))
  · unfold Done
    refine ⟨?_, ?_, ?_⟩
    · calc
        Instance.reduct (execSchema_extension base Γ) JΩ =
            Instance.reduct (execSchema_extension base Γ) IΩ :=
          setPhase₂False_reduct
            (D := D) base Γ hSet
        _ = I := hPhase.1
    · exact setPhase₂False_preserves_not_phase₁
        (D := D) base Γ hSet hPhase.2.1
    · exact setPhase₂False_not_phase₂
        (D := D) base Γ hSet

/- Dispatcher simulation for the second source loop. -/
theorem dispatcher_phase₂_forward
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I J : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₂ (D := D) base IΩ I)
    (hLoop : Cmd.BigStep (.while G₂ Body₂) I J) :
    ∃ JΩ : Instance D (execSchema base Γ),
      Cmd.BigStep
        (.while (loopGuard (D := D) base Γ)
          (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂))
        IΩ JΩ ∧
        Done (D := D) base JΩ J := by
  generalize hW :
      (Whiel.Cmd.«while» G₂ Body₂ : Cmd D Γ) = W at hLoop
  induction hLoop generalizing IΩ G₂ Body₂ with
  | skip I =>
      cases hW
  | assign I X E =>
      cases hW
  | seq h₁ h₂ ih₁ ih₂ =>
      cases hW
  | ite_true hEval hStep ih =>
      cases hW
  | ite_false hEval hStep ih =>
      cases hW
  | while_false hFalse =>
      cases hW
      rcases
        loopBody_phase₂_exit_forward
          (D := D) base
          (G₁ := G₁) (Body₁ := Body₁)
          (Close₁ := Close₁) (Init₂ := Init₂)
          hPhase hFalse with
        ⟨JΩ, hBodyΩ, hDone⟩
      refine ⟨JΩ, ?_, hDone⟩
      exact Cmd.BigStep.while_true
        (Phase₂_loopGuard (D := D) base hPhase)
        hBodyΩ
        (Cmd.BigStep.while_false
          (Done_not_loopGuard (D := D) base hDone))
  | while_true hG hBody hLoop ihBody ihLoop =>
      cases hW
      rcases
        loopBody_phase₂_body_forward
          (D := D) base
          (G₁ := G₁) (Body₁ := Body₁)
          (Close₁ := Close₁) (Init₂ := Init₂)
          hPhase hG hBody with
        ⟨KΩ, hBodyΩ, hKPhase⟩
      rcases ihLoop hKPhase rfl with
        ⟨JΩ, hLoopΩ, hDone⟩
      refine ⟨JΩ, ?_, hDone⟩
      exact Cmd.BigStep.while_true
        (Phase₂_loopGuard (D := D) base hPhase)
        hBodyΩ
        hLoopΩ

/- Dispatcher simulation from phase one through both source
  loops, ending only in `Done`. -/
theorem dispatcher_phase₁_forward
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I J K L M : Instance D Γ}
    {IΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₁ (D := D) base IΩ I)
    (hLoop₁ : Cmd.BigStep (.while G₁ Body₁) I J)
    (hClose : Cmd.BigStep Close₁ J K)
    (hInit₂ : Cmd.BigStep Init₂ K L)
    (hLoop₂ : Cmd.BigStep (.while G₂ Body₂) L M) :
    ∃ MΩ : Instance D (execSchema base Γ),
      Cmd.BigStep
        (.while (loopGuard (D := D) base Γ)
          (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂))
        IΩ MΩ ∧
        Done (D := D) base MΩ M := by
  generalize hW :
      (Whiel.Cmd.«while» G₁ Body₁ : Cmd D Γ) = W at hLoop₁
  induction hLoop₁ generalizing IΩ G₁ Body₁ with
  | skip I =>
      cases hW
  | assign I X E =>
      cases hW
  | seq h₁ h₂ ih₁ ih₂ =>
      cases hW
  | ite_true hEval hStep ih =>
      cases hW
  | ite_false hEval hStep ih =>
      cases hW
  | while_false hFalse =>
      cases hW
      rcases
        loopBody_phase₁_exit_forward
          (D := D) base
          (G₂ := G₂) (Body₂ := Body₂)
          hPhase hFalse hClose hInit₂ with
        ⟨LΩ, hBodyΩ, hLPhase⟩
      rcases
        dispatcher_phase₂_forward
          (D := D) base
          (Close₁ := Close₁) (Init₂ := Init₂)
          hLPhase hLoop₂ with
        ⟨MΩ, hLoopΩ, hDone⟩
      refine ⟨MΩ, ?_, hDone⟩
      exact Cmd.BigStep.while_true
        (Phase₁_loopGuard (D := D) base hPhase)
        hBodyΩ
        hLoopΩ
  | while_true hG hBody hLoop ihBody ihLoop =>
      cases hW
      rcases
        loopBody_phase₁_body_forward
          (D := D) base
          (G₂ := G₂) (Body₂ := Body₂)
          (Close₁ := Close₁) (Init₂ := Init₂)
          hPhase hG hBody with
        ⟨KΩ, hBodyΩ, hKPhase⟩
      rcases
        ihLoop hKPhase hClose rfl with
        ⟨MΩ, hLoopΩ, hDone⟩
      refine ⟨MΩ, ?_, hDone⟩
      exact Cmd.BigStep.while_true
        (Phase₁_loopGuard (D := D) base hPhase)
        hBodyΩ
        hLoopΩ

/- Reverse classification of one dispatcher body step from
  phase two. -/
theorem loopBody_phase₂_reverse
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I : Instance D Γ}
    {IΩ JΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₂ (D := D) base IΩ I)
    (hStep :
      Cmd.BigStep
        (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
        IΩ JΩ) :
    (∃ J : Instance D Γ,
      G₂.eval I ∧
        Cmd.BigStep Body₂ I J ∧
          Phase₂ (D := D) base JΩ J) ∨
      (¬ G₂.eval I ∧ Done (D := D) base JΩ I) := by
  have hOuter :
      ((phase₁Guard (D := D) base Γ).eval IΩ ∧
          Cmd.BigStep
            (phase₁Branch base G₁ Body₁ Close₁ Init₂)
            IΩ JΩ) ∨
        (¬ (phase₁Guard (D := D) base Γ).eval IΩ ∧
          Cmd.BigStep (phase₂Branch base G₂ Body₂)
            IΩ JΩ) := by
    exact
      (Cmd.bigStep_ite_iff
        (phase₁Guard (D := D) base Γ)
        (phase₁Branch base G₁ Body₁ Close₁ Init₂)
        (phase₂Branch base G₂ Body₂)
        IΩ JΩ).mp
        (by simpa [loopBody] using hStep)
  cases hOuter with
  | inl h =>
      exact False.elim (hPhase.2.1 h.1)
  | inr h =>
      have hInner :
          ((liftGuard (D := D) base Γ G₂).eval IΩ ∧
              Cmd.BigStep (liftCmd base Γ Body₂) IΩ JΩ) ∨
            (¬ (liftGuard (D := D) base Γ G₂).eval IΩ ∧
              Cmd.BigStep (setPhase₂False (D := D) base Γ)
                IΩ JΩ) := by
        exact
          (Cmd.bigStep_ite_iff
            (liftGuard (D := D) base Γ G₂)
            (liftCmd base Γ Body₂)
            (setPhase₂False (D := D) base Γ)
            IΩ JΩ).mp
            (by simpa [phase₂Branch] using h.2)
      cases hInner with
      | inl hRun =>
          let J : Instance D Γ :=
            Instance.reduct (execSchema_extension base Γ) JΩ
          have hG : G₂.eval I := by
            have hSrc :=
              (liftGuard_eval_iff
                (D := D) base Γ G₂ IΩ).mp hRun.1
            simpa [hPhase.1] using hSrc
          have hBody :
              Cmd.BigStep Body₂ I J := by
            simpa [J, hPhase.1] using
              (liftCmd_bigStep_reduct
                (D := D) base Γ hRun.2)
          have hPhaseJ :
              Phase₂ (D := D) base JΩ J := by
            unfold Phase₂
            refine ⟨rfl, ?_, ?_⟩
            · intro hPhase₁
              exact hPhase.2.1
                ((liftCmd_preserves_phase₁Guard
                  (D := D) base Γ Body₂ hRun.2).mp
                  hPhase₁)
            · exact
                (liftCmd_preserves_phase₂Guard
                  (D := D) base Γ Body₂ hRun.2).mpr
                  hPhase.2.2
          exact Or.inl ⟨J, hG, hBody, hPhaseJ⟩
      | inr hExit =>
          have hNotG : ¬ G₂.eval I := by
            intro hG
            apply hExit.1
            exact
              (liftGuard_eval_iff
                (D := D) base Γ G₂ IΩ).mpr
                (by simpa [hPhase.1] using hG)
          have hDone :
              Done (D := D) base JΩ I := by
            unfold Done
            refine ⟨?_, ?_, ?_⟩
            · calc
                Instance.reduct (execSchema_extension base Γ) JΩ =
                    Instance.reduct (execSchema_extension base Γ) IΩ :=
                  setPhase₂False_reduct
                    (D := D) base Γ hExit.2
                _ = I := hPhase.1
            · exact setPhase₂False_preserves_not_phase₁
                (D := D) base Γ hExit.2 hPhase.2.1
            · exact setPhase₂False_not_phase₂
                (D := D) base Γ hExit.2
          exact Or.inr ⟨hNotG, hDone⟩

/- Reverse the phase-one exit block into source close and
  second-loop initialization runs. -/
theorem finishFirstBranch_bigStep_phase₂_reverse
    (base : A)
    {Close₁ Init₂ : Cmd D Γ}
    {I : Instance D Γ}
    {IΩ KΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₁ (D := D) base IΩ I)
    (hStep :
      Cmd.BigStep (finishFirstBranch base Close₁ Init₂)
        IΩ KΩ) :
    ∃ J K : Instance D Γ,
      Cmd.BigStep Close₁ I J ∧
        Cmd.BigStep Init₂ J K ∧
          Phase₂ (D := D) base KΩ K := by
  have hSeq :
      Cmd.BigStep
        (Cmd.seqList
          [ liftCmd base Γ Close₁,
            liftCmd base Γ Init₂,
            setPhase₁False (D := D) base Γ,
            setPhase₂True (D := D) base Γ ])
        IΩ KΩ := by
    simpa [finishFirstBranch] using hStep
  rw [Cmd.seqList, Cmd.bigStep_seq_iff] at hSeq
  rcases hSeq with ⟨JΩ, hCloseΩ, hRest₁⟩
  change
    Cmd.BigStep
      (.seq (liftCmd base Γ Init₂)
        (Cmd.seqList
          [ setPhase₁False (D := D) base Γ,
            setPhase₂True (D := D) base Γ ]))
      JΩ KΩ at hRest₁
  rw [Cmd.bigStep_seq_iff] at hRest₁
  rcases hRest₁ with ⟨K1Ω, hInitΩ, hRest₂⟩
  change
    Cmd.BigStep
      (.seq (setPhase₁False (D := D) base Γ)
        (Cmd.seqList
          [setPhase₂True (D := D) base Γ]))
      K1Ω KΩ at hRest₂
  rw [Cmd.bigStep_seq_iff] at hRest₂
  rcases hRest₂ with ⟨K2Ω, hSet1, hRest₃⟩
  change
    Cmd.BigStep
      (.seq (setPhase₂True (D := D) base Γ)
        (Cmd.seqList ([] : List (Cmd D (execSchema base Γ)))))
      K2Ω KΩ at hRest₃
  rw [Cmd.bigStep_seq_iff] at hRest₃
  rcases hRest₃ with ⟨K3Ω, hSet2, hSkip⟩
  have hKΩ : KΩ = K3Ω :=
    (Cmd.bigStep_skip_iff K3Ω KΩ).mp
      (by simpa [Cmd.seqList] using hSkip)
  let J : Instance D Γ :=
    Instance.reduct (execSchema_extension base Γ) JΩ
  let K : Instance D Γ :=
    Instance.reduct (execSchema_extension base Γ) K1Ω
  have hCloseSrc :
      Cmd.BigStep Close₁ I J := by
    simpa [J, hPhase.1] using
      (liftCmd_bigStep_reduct
        (D := D) base Γ hCloseΩ)
  have hInitSrc :
      Cmd.BigStep Init₂ J K := by
    simpa [J, K] using
      (liftCmd_bigStep_reduct
        (D := D) base Γ hInitΩ)
  have hPhaseK :
      Phase₂ (D := D) base KΩ K := by
    rw [hKΩ]
    unfold Phase₂
    refine ⟨?_, ?_, ?_⟩
    · calc
        Instance.reduct (execSchema_extension base Γ) K3Ω =
            Instance.reduct (execSchema_extension base Γ) K2Ω :=
          setPhase₂True_reduct
            (D := D) base Γ hSet2
        _ = Instance.reduct (execSchema_extension base Γ) K1Ω :=
          setPhase₁False_reduct
            (D := D) base Γ hSet1
        _ = K := rfl
    · exact setPhase₂True_preserves_not_phase₁
        (D := D) base Γ hSet2
        (setPhase₁False_not_phase₁
          (D := D) base Γ hSet1)
    · exact setPhase₂True_phase₂
        (D := D) base Γ hSet2
  exact ⟨J, K, hCloseSrc, hInitSrc, hPhaseK⟩

/- Reverse classification of one dispatcher body step from
  phase one. -/
theorem loopBody_phase₁_reverse
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I : Instance D Γ}
    {IΩ JΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₁ (D := D) base IΩ I)
    (hStep :
      Cmd.BigStep
        (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
        IΩ JΩ) :
    (∃ J : Instance D Γ,
      G₁.eval I ∧
        Cmd.BigStep Body₁ I J ∧
          Phase₁ (D := D) base JΩ J) ∨
      (∃ J K : Instance D Γ,
        ¬ G₁.eval I ∧
          Cmd.BigStep Close₁ I J ∧
            Cmd.BigStep Init₂ J K ∧
              Phase₂ (D := D) base JΩ K) := by
  have hOuter :
      ((phase₁Guard (D := D) base Γ).eval IΩ ∧
          Cmd.BigStep
            (phase₁Branch base G₁ Body₁ Close₁ Init₂)
            IΩ JΩ) ∨
        (¬ (phase₁Guard (D := D) base Γ).eval IΩ ∧
          Cmd.BigStep (phase₂Branch base G₂ Body₂)
            IΩ JΩ) := by
    exact
      (Cmd.bigStep_ite_iff
        (phase₁Guard (D := D) base Γ)
        (phase₁Branch base G₁ Body₁ Close₁ Init₂)
        (phase₂Branch base G₂ Body₂)
        IΩ JΩ).mp
        (by simpa [loopBody] using hStep)
  cases hOuter with
  | inr h =>
      exact False.elim (h.1 hPhase.2.1)
  | inl h =>
      have hInner :
          ((liftGuard (D := D) base Γ G₁).eval IΩ ∧
              Cmd.BigStep (liftCmd base Γ Body₁) IΩ JΩ) ∨
            (¬ (liftGuard (D := D) base Γ G₁).eval IΩ ∧
              Cmd.BigStep
                (finishFirstBranch base Close₁ Init₂)
                IΩ JΩ) := by
        exact
          (Cmd.bigStep_ite_iff
            (liftGuard (D := D) base Γ G₁)
            (liftCmd base Γ Body₁)
            (finishFirstBranch base Close₁ Init₂)
            IΩ JΩ).mp
            (by simpa [phase₁Branch] using h.2)
      cases hInner with
      | inl hRun =>
          let J : Instance D Γ :=
            Instance.reduct (execSchema_extension base Γ) JΩ
          have hG : G₁.eval I := by
            have hSrc :=
              (liftGuard_eval_iff
                (D := D) base Γ G₁ IΩ).mp hRun.1
            simpa [hPhase.1] using hSrc
          have hBody :
              Cmd.BigStep Body₁ I J := by
            simpa [J, hPhase.1] using
              (liftCmd_bigStep_reduct
                (D := D) base Γ hRun.2)
          have hPhaseJ :
              Phase₁ (D := D) base JΩ J := by
            unfold Phase₁
            refine ⟨rfl, ?_, ?_⟩
            · exact
                (liftCmd_preserves_phase₁Guard
                  (D := D) base Γ Body₁ hRun.2).mpr
                  hPhase.2.1
            · intro hPhase₂
              exact hPhase.2.2
                ((liftCmd_preserves_phase₂Guard
                  (D := D) base Γ Body₁ hRun.2).mp
                  hPhase₂)
          exact Or.inl ⟨J, hG, hBody, hPhaseJ⟩
      | inr hExit =>
          have hNotG : ¬ G₁.eval I := by
            intro hG
            apply hExit.1
            exact
              (liftGuard_eval_iff
                (D := D) base Γ G₁ IΩ).mpr
                (by simpa [hPhase.1] using hG)
          rcases
            finishFirstBranch_bigStep_phase₂_reverse
              (D := D) base hPhase hExit.2 with
            ⟨J, K, hClose, hInit, hPhaseK⟩
          exact Or.inr
            ⟨J, K, hNotG, hClose, hInit, hPhaseK⟩

/- Reverse dispatcher simulation from phase two. -/
theorem dispatcher_phase₂_reverse
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I K : Instance D Γ}
    {IΩ KΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₂ (D := D) base IΩ I)
    (hStep :
      Cmd.BigStep
        (.while (loopGuard (D := D) base Γ)
          (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂))
        IΩ KΩ)
    (hDone : Done (D := D) base KΩ K) :
    Cmd.BigStep (.while G₂ Body₂) I K := by
  generalize hW :
      (Whiel.Cmd.«while» (loopGuard (D := D) base Γ)
        (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂) :
          Cmd D (execSchema base Γ)) = W at hStep
  induction hStep generalizing I K G₂ Body₂ with
  | skip I =>
      cases hW
  | assign I X E =>
      cases hW
  | seq h₁ h₂ ih₁ ih₂ =>
      cases hW
  | ite_true hEval hStep ih =>
      cases hW
  | ite_false hEval hStep ih =>
      cases hW
  | while_false hFalse =>
      cases hW
      exact False.elim
        (hFalse (Phase₂_loopGuard (D := D) base hPhase))
  | while_true hGuard hBody hLoop ihBody ihLoop =>
      cases hW
      have hClass :=
        loopBody_phase₂_reverse
          (D := D) base
          (G₁ := G₁) (Body₁ := Body₁)
          (Close₁ := Close₁) (Init₂ := Init₂)
          hPhase hBody
      cases hClass with
      | inl hRun =>
          rcases hRun with
            ⟨J, hG, hBodySrc, hJPhase⟩
          have hTail :
              Cmd.BigStep (.while G₂ Body₂) J K :=
            ihLoop hJPhase hDone rfl
          exact Cmd.BigStep.while_true hG hBodySrc hTail
      | inr hExit =>
          rcases hExit with ⟨hNotG, hDone₁⟩
          have hTail :=
            (Cmd.bigStep_while_iff
              (loopGuard (D := D) base Γ)
              (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
              _ _).mp hLoop
          have hK : K = I := by
            cases hTail with
            | inl hStop =>
                calc
                  K =
                      Instance.reduct
                        (execSchema_extension base Γ) _ :=
                    hDone.1.symm
                  _ =
                      Instance.reduct
                        (execSchema_extension base Γ) _ := by
                    rw [hStop.2]
                  _ = I := hDone₁.1
            | inr hMore =>
                rcases hMore with ⟨_, hMoreGuard, _, _⟩
                exact False.elim
                  ((Done_not_loopGuard
                    (D := D) base hDone₁) hMoreGuard)
          rw [hK]
          exact Cmd.BigStep.while_false hNotG

/- Reverse dispatcher simulation from phase one. -/
theorem dispatcher_phase₁_reverse
    (base : A)
    {G₁ : Guard D Γ}
    {Body₁ Close₁ Init₂ : Cmd D Γ}
    {G₂ : Guard D Γ}
    {Body₂ : Cmd D Γ}
    {I K : Instance D Γ}
    {IΩ KΩ : Instance D (execSchema base Γ)}
    (hPhase : Phase₁ (D := D) base IΩ I)
    (hStep :
      Cmd.BigStep
        (.while (loopGuard (D := D) base Γ)
          (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂))
        IΩ KΩ)
    (hDone : Done (D := D) base KΩ K) :
    ∃ J L M : Instance D Γ,
      Cmd.BigStep (.while G₁ Body₁) I J ∧
        Cmd.BigStep Close₁ J L ∧
          Cmd.BigStep Init₂ L M ∧
            Cmd.BigStep (.while G₂ Body₂) M K := by
  generalize hW :
      (Whiel.Cmd.«while» (loopGuard (D := D) base Γ)
        (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂) :
          Cmd D (execSchema base Γ)) = W at hStep
  induction hStep generalizing I K G₁ Body₁ with
  | skip I =>
      cases hW
  | assign I X E =>
      cases hW
  | seq h₁ h₂ ih₁ ih₂ =>
      cases hW
  | ite_true hEval hStep ih =>
      cases hW
  | ite_false hEval hStep ih =>
      cases hW
  | while_false hFalse =>
      cases hW
      exact False.elim
        (hFalse (Phase₁_loopGuard (D := D) base hPhase))
  | while_true hGuard hBody hLoop ihBody ihLoop =>
      cases hW
      have hClass :=
        loopBody_phase₁_reverse
          (D := D) base
          (G₂ := G₂) (Body₂ := Body₂)
          hPhase hBody
      cases hClass with
      | inl hRun =>
          rcases hRun with
            ⟨J, hG, hBodySrc, hJPhase⟩
          rcases ihLoop hJPhase hDone rfl with
            ⟨L, M, N, hLoop₁, hClose, hInit, hLoop₂⟩
          exact
            ⟨L, M, N,
              Cmd.BigStep.while_true hG hBodySrc hLoop₁,
              hClose, hInit, hLoop₂⟩
      | inr hExit =>
          rcases hExit with
            ⟨J, L, hNotG, hClose, hInit, hLPhase⟩
          have hLoop₂ :
              Cmd.BigStep (.while G₂ Body₂) L K :=
            dispatcher_phase₂_reverse
              (D := D) base
              (G₁ := G₁) (Body₁ := Body₁)
              (Close₁ := Close₁) (Init₂ := Init₂)
              hLPhase hLoop hDone
          exact
            ⟨I, J, L,
              Cmd.BigStep.while_false hNotG,
              hClose, hInit, hLoop₂⟩

/- A terminating while run ends where its guard is false. -/
theorem while_final_not_guard
    {Ω : UnnamedSchema A}
    {G : Guard D Ω}
    {C : Cmd D Ω}
    {I J : Instance D Ω}
    (hStep : Cmd.BigStep (.while G C) I J) :
    ¬ G.eval J := by
  generalize hW :
      (Whiel.Cmd.«while» G C : Cmd D Ω) = W at hStep
  induction hStep generalizing G C with
  | skip I =>
      cases hW
  | assign I X E =>
      cases hW
  | seq h₁ h₂ ih₁ ih₂ =>
      cases hW
  | ite_true hEval hStep ih =>
      cases hW
  | ite_false hEval hStep ih =>
      cases hW
  | while_false hFalse =>
      cases hW
      exact hFalse
  | while_true hEval hBody hLoop ihBody ihLoop =>
      cases hW
      exact ihLoop rfl

/- Same-schema programs are semantically the same as their
  underlying command. -/
theorem Program.ofCmd_bigStep_iff
    (C : Cmd D Γ)
    (I K : Instance D Γ) :
    (Program.ofCmd C).BigStep I K ↔
      Cmd.BigStep C I K := by
  constructor
  · rintro ⟨J, hStep, hObs⟩
    have hInit :
        (Program.ofCmd C).initialInstance I = I := by
      simp [Program.initialInstance, Program.ofCmd,
        Instance.expandEmpty_refl]
    have hJ : J = K := by
      simpa [Program.observe, Program.ofCmd] using hObs
    rw [hInit] at hStep
    subst K
    simpa [Program.ofCmd] using hStep
  · intro hStep
    refine ⟨K, ?_, ?_⟩
    · simpa [Program.ofCmd, Program.initialInstance,
        Instance.expandEmpty_refl] using hStep
    · simp [Program.observe, Program.ofCmd]

/- Disjoint assignment can be used as a membership
  non-overlap fact. -/
private theorem disjointAssignments_iff
    {Ω : UnnamedSchema A}
    (C₁ C₂ : Cmd D Ω) :
    Cmd.DisjointAssignments C₁ C₂ ↔
      ∀ X,
        X ∈ C₁.assignedSymbols →
          X ∈ C₂.assignedSymbols → False := by
  constructor
  · intro hDis X hX₁ hX₂
    have hMem :
        X ∈ C₁.assignedSymbols ∩ C₂.assignedSymbols :=
      Finset.mem_inter.mpr ⟨hX₁, hX₂⟩
    rw [hDis] at hMem
    simp at hMem
  · intro hDis
    unfold Cmd.DisjointAssignments
    ext X
    constructor
    · intro hX
      rcases Finset.mem_inter.mp hX with ⟨hX₁, hX₂⟩
      exact False.elim (hDis X hX₁ hX₂)
    · intro hX
      simp at hX

/- A raw symbol is assigned by a sequenced list exactly
  when it is assigned by one list element. -/
private theorem assignedSymbols_seqList_mem
    {Ω : UnnamedSchema A}
    (Cs : List (Cmd D Ω))
    (X : A) :
    X ∈ (Cmd.seqList Cs).assignedSymbols ↔
      ∃ C : Cmd D Ω, C ∈ Cs ∧
        X ∈ C.assignedSymbols := by
  induction Cs with
  | nil =>
      simp [Cmd.seqList, Cmd.assignedSymbols]
  | cons C Cs ih =>
      constructor
      · intro hX
        have hCases :
            X ∈ C.assignedSymbols ∨
              X ∈ (Cmd.seqList Cs).assignedSymbols := by
          simpa [Cmd.seqList, Cmd.assignedSymbols]
            using hX
        rcases hCases with hHead | hTail
        · exact ⟨C, by simp, hHead⟩
        · rcases ih.mp hTail with ⟨C', hC', hX'⟩
          exact ⟨C', by simp [hC'], hX'⟩
      · rintro ⟨C', hC', hX'⟩
        rcases List.mem_cons.mp hC' with hEq | hTail
        · subst hEq
          simp [Cmd.seqList, Cmd.assignedSymbols, hX']
        · have hTailAssigned :
              X ∈ (Cmd.seqList Cs).assignedSymbols :=
            ih.mpr ⟨C', hTail, hX'⟩
          simp [Cmd.seqList, Cmd.assignedSymbols,
            hTailAssigned]

/- Flattening and resequencing preserves assigned names. -/
@[simp] private theorem assignedSymbols_seqList_flattenSeq
    {Ω : UnnamedSchema A}
    (C : Cmd D Ω) :
    (Cmd.seqList C.flattenSeq).assignedSymbols =
      C.assignedSymbols := by
  induction C with
  | skip =>
      simp [Cmd.flattenSeq, Cmd.seqList,
        Cmd.assignedSymbols]
  | assign X e =>
      simp [Cmd.flattenSeq, Cmd.seqList,
        Cmd.assignedSymbols]
  | seq C₁ C₂ ih₁ ih₂ =>
      ext X
      constructor
      · intro hX
        have hX' :
            X ∈
              (Cmd.seqList
                (C₁.flattenSeq ++ C₂.flattenSeq)).assignedSymbols := by
          simpa [Cmd.flattenSeq] using hX
        rcases
            (assignedSymbols_seqList_mem
              (C₁.flattenSeq ++ C₂.flattenSeq) X).mp hX'
          with ⟨C, hC, hXC⟩
        rcases List.mem_append.mp hC with hLeft | hRight
        · have hAssigned :
              X ∈ C₁.assignedSymbols := by
            rw [← ih₁]
            exact
              (assignedSymbols_seqList_mem C₁.flattenSeq X).mpr
                ⟨C, hLeft, hXC⟩
          simpa [Cmd.assignedSymbols] using
            Or.inl hAssigned
        · have hAssigned :
              X ∈ C₂.assignedSymbols := by
            rw [← ih₂]
            exact
              (assignedSymbols_seqList_mem C₂.flattenSeq X).mpr
                ⟨C, hRight, hXC⟩
          simpa [Cmd.assignedSymbols] using
            Or.inr hAssigned
      · intro hX
        have hCases :
            X ∈ C₁.assignedSymbols ∨
              X ∈ C₂.assignedSymbols := by
          simpa [Cmd.assignedSymbols] using hX
        rcases hCases with hLeft | hRight
        · have hSeq :
              X ∈ (Cmd.seqList C₁.flattenSeq).assignedSymbols := by
            rw [ih₁]
            exact hLeft
          rcases
              (assignedSymbols_seqList_mem C₁.flattenSeq X).mp
                hSeq with
            ⟨C, hC, hXC⟩
          have hAppend :
              X ∈
                (Cmd.seqList
                  (C₁.flattenSeq ++
                    C₂.flattenSeq)).assignedSymbols :=
            (assignedSymbols_seqList_mem
              (C₁.flattenSeq ++ C₂.flattenSeq) X).mpr
              ⟨C, List.mem_append.mpr (Or.inl hC), hXC⟩
          simpa [Cmd.flattenSeq] using hAppend
        · have hSeq :
              X ∈ (Cmd.seqList C₂.flattenSeq).assignedSymbols := by
            rw [ih₂]
            exact hRight
          rcases
              (assignedSymbols_seqList_mem C₂.flattenSeq X).mp
                hSeq with
            ⟨C, hC, hXC⟩
          have hAppend :
              X ∈
                (Cmd.seqList
                  (C₁.flattenSeq ++
                    C₂.flattenSeq)).assignedSymbols :=
            (assignedSymbols_seqList_mem
              (C₁.flattenSeq ++ C₂.flattenSeq) X).mpr
              ⟨C, List.mem_append.mpr (Or.inr hC), hXC⟩
          simpa [Cmd.flattenSeq] using hAppend
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [Cmd.flattenSeq, Cmd.seqList,
        Cmd.assignedSymbols]
  | «while» G C ih =>
      simp [Cmd.flattenSeq, Cmd.seqList,
        Cmd.assignedSymbols]

/- Assignment uniqueness is preserved by retagging. -/
private theorem assignedAtMostOnce_onExtension
    {Ω Ω' : UnnamedSchema A}
    (hExt : Ω'.extensionOf Ω)
    (C : Cmd D Ω) :
    (C.onExtension hExt).AssignedAtMostOnce ↔
      C.AssignedAtMostOnce := by
  induction C with
  | skip =>
      simp [Cmd.onExtension, Cmd.AssignedAtMostOnce]
  | assign X e =>
      simp [Cmd.onExtension, Cmd.AssignedAtMostOnce]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [Cmd.onExtension, Cmd.AssignedAtMostOnce,
        Cmd.DisjointAssignments, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [Cmd.onExtension, Cmd.AssignedAtMostOnce,
        Cmd.DisjointAssignments, ih₁, ih₂]
  | «while» G C ih =>
      simp [Cmd.onExtension, Cmd.AssignedAtMostOnce, ih]

/- Cleaning one sequence preserves assignment uniqueness. -/
private theorem assignedAtMostOnce_cleanSeq
    {Ω : UnnamedSchema A}
    (C₁ C₂ : Cmd D Ω) :
    (Cmd.cleanSeq C₁ C₂).AssignedAtMostOnce ↔
      (.seq C₁ C₂ : Cmd D Ω).AssignedAtMostOnce := by
  induction C₁ generalizing C₂
  <;> cases C₂
  <;> simp [Cmd.cleanSeq, Cmd.AssignedAtMostOnce,
    Cmd.DisjointAssignments, Cmd.assignedSymbols, *,
    ← Finset.disjoint_iff_inter_eq_empty,
    and_assoc, and_left_comm, and_comm]

/- Cleaning preserves assignment uniqueness. -/
private theorem assignedAtMostOnce_clean
    {Ω : UnnamedSchema A}
    (C : Cmd D Ω) :
    C.clean.AssignedAtMostOnce ↔ C.AssignedAtMostOnce := by
  induction C with
  | skip =>
      simp [Cmd.clean, Cmd.AssignedAtMostOnce]
  | assign X e =>
      simp [Cmd.clean, Cmd.AssignedAtMostOnce]
  | seq C₁ C₂ ih₁ ih₂ =>
      rw [Cmd.clean]
      rw [assignedAtMostOnce_cleanSeq]
      simp [Cmd.AssignedAtMostOnce,
        Cmd.DisjointAssignments, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [Cmd.clean, Cmd.AssignedAtMostOnce,
        Cmd.DisjointAssignments, ih₁, ih₂]
  | «while» G C ih =>
      simp [Cmd.clean, Cmd.AssignedAtMostOnce, ih]

/- Lifted commands preserve assignment uniqueness. -/
private theorem assignedAtMostOnce_liftCmd
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ) :
    (liftCmd base Γ C).AssignedAtMostOnce ↔
      C.AssignedAtMostOnce := by
  unfold liftCmd
  rw [assignedAtMostOnce_onExtension]
  exact assignedAtMostOnce_clean C

/- Lifted commands preserve preamble safety. -/
private theorem preambleSPSafe_liftCmd
    (base : A)
    (Γ : UnnamedSchema A)
    (C : Cmd D Γ) :
    (liftCmd base Γ C).PreambleSPSafe ↔
      C.PreambleSPSafe := by
  unfold Cmd.PreambleSPSafe
  exact and_congr
    (loopFree_liftCmd base Γ C)
    (assignedAtMostOnce_liftCmd base Γ C)

/- Loop-free commands contribute no top-level loop when
  flattened. -/
private theorem loopFree_of_mem_flattenSeq
    {Ω : UnnamedSchema A}
    {C C' : Cmd D Ω}
    (hC : C.LoopFree)
    (hMem : C' ∈ C.flattenSeq) :
    C'.LoopFree := by
  induction C with
  | skip =>
      simp [Cmd.flattenSeq] at hMem
  | assign X e =>
      have hEq : C' = .assign X e := by
        simpa [Cmd.flattenSeq] using hMem
      cases hEq
      exact hC
  | seq C₁ C₂ ih₁ ih₂ =>
      have hCases :
          C' ∈ C₁.flattenSeq ∨
            C' ∈ C₂.flattenSeq := by
        simpa [Cmd.flattenSeq] using hMem
      rcases hCases with hLeft | hRight
      · exact ih₁ hC.1 hLeft
      · exact ih₂ hC.2 hRight
  | ite G C₁ C₂ ih₁ ih₂ =>
      have hEq : C' = .ite G C₁ C₂ := by
        simpa [Cmd.flattenSeq] using hMem
      subst hEq
      exact hC
  | «while» G C ih =>
      exact False.elim hC

/- Flattening and resequencing preserves loop-freedom in
  the forward direction needed by the recognizer. -/
private theorem loopFree_seqList_flattenSeq
    {Ω : UnnamedSchema A}
    {C : Cmd D Ω}
    (hC : C.LoopFree) :
    (Cmd.seqList C.flattenSeq).LoopFree := by
  rw [Cmd.loopFree_seqList_iff]
  intro C' hMem
  exact loopFree_of_mem_flattenSeq hC hMem

/- Sequencing appended command lists preserves assignment
  uniqueness under disjoint assigned-name sets. -/
private theorem assignedAtMostOnce_seqList_append
    {Ω : UnnamedSchema A}
    {Cs Ds : List (Cmd D Ω)}
    (hCs : (Cmd.seqList Cs).AssignedAtMostOnce)
    (hDs : (Cmd.seqList Ds).AssignedAtMostOnce)
    (hDis :
      Cmd.DisjointAssignments
        (Cmd.seqList Cs) (Cmd.seqList Ds)) :
    (Cmd.seqList (Cs ++ Ds)).AssignedAtMostOnce := by
  induction Cs with
  | nil =>
      simpa [Cmd.seqList] using hDs
  | cons C Cs ih =>
      have hTailDis :
          Cmd.DisjointAssignments
            (Cmd.seqList Cs) (Cmd.seqList Ds) := by
        apply (disjointAssignments_iff _ _).mpr
        intro X hXCs hXDs
        exact
          ((disjointAssignments_iff _ _).mp hDis)
            X
            (by
              simpa [Cmd.seqList, Cmd.assignedSymbols]
                using Or.inr hXCs)
            hXDs
      have hTail :
          (Cmd.seqList (Cs ++ Ds)).AssignedAtMostOnce :=
        ih hCs.2.1 hTailDis
      refine ⟨hCs.1, hTail, ?_⟩
      apply (disjointAssignments_iff _ _).mpr
      intro X hXC hXTail
      rcases
          (assignedSymbols_seqList_mem (Cs ++ Ds) X).mp
            hXTail with
        ⟨C', hC', hXC'⟩
      rcases List.mem_append.mp hC' with hInCs | hInDs
      · exact
          ((disjointAssignments_iff _ _).mp hCs.2.2)
            X hXC
            ((assignedSymbols_seqList_mem Cs X).mpr
              ⟨C', hInCs, hXC'⟩)
      · exact
          ((disjointAssignments_iff _ _).mp hDis)
            X
            (by
              simpa [Cmd.seqList, Cmd.assignedSymbols]
                using Or.inl hXC)
            ((assignedSymbols_seqList_mem Ds X).mpr
              ⟨C', hInDs, hXC'⟩)

/- Flattening and resequencing preserves assignment
  uniqueness in the forward direction needed by the
  recognizer. -/
private theorem assignedAtMostOnce_seqList_flattenSeq
    {Ω : UnnamedSchema A}
    {C : Cmd D Ω}
    (hC : C.AssignedAtMostOnce) :
    (Cmd.seqList C.flattenSeq).AssignedAtMostOnce := by
  induction C with
  | skip =>
      simp [Cmd.flattenSeq, Cmd.seqList,
        Cmd.AssignedAtMostOnce]
  | assign X e =>
      simp [Cmd.flattenSeq, Cmd.seqList,
        Cmd.AssignedAtMostOnce, Cmd.DisjointAssignments,
        Cmd.assignedSymbols]
  | seq C₁ C₂ ih₁ ih₂ =>
      rw [Cmd.flattenSeq]
      apply assignedAtMostOnce_seqList_append
      · exact ih₁ hC.1
      · exact ih₂ hC.2.1
      · apply (disjointAssignments_iff _ _).mpr
        intro X hX₁ hX₂
        exact
          ((disjointAssignments_iff _ _).mp hC.2.2)
            X
            (by
              simpa [assignedSymbols_seqList_flattenSeq]
                using hX₁)
            (by
              simpa [assignedSymbols_seqList_flattenSeq]
                using hX₂)
  | ite G C₁ C₂ ih₁ ih₂ =>
      simpa [Cmd.flattenSeq, Cmd.seqList,
        Cmd.AssignedAtMostOnce, Cmd.DisjointAssignments,
        Cmd.assignedSymbols] using hC
  | «while» G C ih =>
      simpa [Cmd.flattenSeq, Cmd.seqList,
        Cmd.AssignedAtMostOnce, Cmd.DisjointAssignments,
        Cmd.assignedSymbols] using hC

/- Flattening and resequencing preserves preamble safety in
  the forward direction needed by the recognizer. -/
private theorem preambleSPSafe_seqList_flattenSeq
    {Ω : UnnamedSchema A}
    {C : Cmd D Ω}
    (hC : C.PreambleSPSafe) :
    (Cmd.seqList C.flattenSeq).PreambleSPSafe :=
  ⟨loopFree_seqList_flattenSeq hC.1,
    assignedAtMostOnce_seqList_flattenSeq hC.2⟩

@[simp] private theorem mem_assigned_setPhase₁True
    (base : A)
    (Γ : UnnamedSchema A)
    (X : A) :
    X ∈
        (setPhase₁True (D := D) base Γ).assignedSymbols ↔
      X = (phase₁Sym base Γ).1 := by
  simp [setPhase₁True, assignTrue, Cmd.assignedSymbols]

@[simp] private theorem mem_assigned_setPhase₂False
    (base : A)
    (Γ : UnnamedSchema A)
    (X : A) :
    X ∈
        (setPhase₂False (D := D) base Γ).assignedSymbols ↔
      X = (phase₂Sym base Γ).1 := by
  simp [setPhase₂False, assignFalse, Cmd.assignedSymbols]

/- The generated initialization block assigns each relation
  at most once. -/
private theorem assignedAtMostOnce_initBlock
    (base : A)
    {Init₁ : Cmd D Γ}
    (hInit₁ : Init₁.AssignedAtMostOnce) :
    (initBlock base Init₁).AssignedAtMostOnce := by
  unfold initBlock
  change
    (Cmd.seq
      (liftCmd base Γ Init₁)
      (Cmd.seq
        (setPhase₁True (D := D) base Γ)
        (Cmd.seq
          (setPhase₂False (D := D) base Γ)
          Cmd.skip))).AssignedAtMostOnce
  refine
    ⟨(assignedAtMostOnce_liftCmd base Γ Init₁).mpr
        hInit₁,
      ?_, ?_⟩
  · refine ⟨by simp [setPhase₁True, assignTrue,
        Cmd.AssignedAtMostOnce],
      ?_, ?_⟩
    · refine ⟨by simp [setPhase₂False, assignFalse,
          Cmd.AssignedAtMostOnce],
        by simp [Cmd.AssignedAtMostOnce], ?_⟩
      apply (disjointAssignments_iff _ _).mpr
      intro X hX hSkip
      simp [Cmd.assignedSymbols] at hSkip
    · apply (disjointAssignments_iff _ _).mpr
      intro X hX₁ hXTail
      have hX₁eq : X = (phase₁Sym base Γ).1 :=
        (mem_assigned_setPhase₁True base Γ X).mp hX₁
      subst X
      have hCases :
          (phase₁Sym base Γ).1 ∈
              (setPhase₂False
                (D := D) base Γ).assignedSymbols ∨
            (phase₁Sym base Γ).1 ∈
              (Cmd.skip :
                Cmd D (execSchema base Γ)).assignedSymbols := by
        simpa [Cmd.assignedSymbols] using hXTail
      rcases hCases with hP₂ | hSkip
      · have hRaw :
            (phase₁Sym base Γ).1 =
              (phase₂Sym base Γ).1 :=
          (mem_assigned_setPhase₂False base Γ
            (phase₁Sym base Γ).1).mp hP₂
        exact
          phase₁Sym_ne_phase₂Sym base Γ
            (Subtype.ext hRaw)
      · simp [Cmd.assignedSymbols] at hSkip
  · apply (disjointAssignments_iff _ _).mpr
    intro X hXLift hXTail
    have hSource : X ∈ Γ.syms := by
      have hXInit : X ∈ Init₁.assignedSymbols := by
        simpa [assignedSymbols_liftCmd] using hXLift
      exact Cmd.assignedSymbols_subset_syms Init₁ hXInit
    have hCases :
        X ∈
            (setPhase₁True
              (D := D) base Γ).assignedSymbols ∨
          X ∈
            (Cmd.seq
              (setPhase₂False (D := D) base Γ)
              (Cmd.skip :
                Cmd D (execSchema base Γ))).assignedSymbols := by
      simpa [Cmd.assignedSymbols] using hXTail
    rcases hCases with hP₁ | hTail
    · have hEq : X = (phase₁Sym base Γ).1 :=
        (mem_assigned_setPhase₁True base Γ X).mp hP₁
      subst X
      exact phase₁Sym_not_mem base Γ hSource
    · have hTailCases :
          X ∈
              (setPhase₂False
                (D := D) base Γ).assignedSymbols ∨
            X ∈
              (Cmd.skip :
                Cmd D (execSchema base Γ)).assignedSymbols := by
        simpa [Cmd.assignedSymbols] using hTail
      rcases hTailCases with hP₂ | hSkip
      · have hEq : X = (phase₂Sym base Γ).1 :=
          (mem_assigned_setPhase₂False base Γ X).mp hP₂
        subst X
        exact phase₂Sym_not_mem base Γ hSource
      · simp [Cmd.assignedSymbols] at hSkip

/- The generated initialization block is preamble-safe when
  the first source preamble is safe. -/
private theorem initBlock_preambleSPSafe
    (base : A)
    {Init₁ : Cmd D Γ}
    (hInit₁ : Init₁.PreambleSPSafe) :
    (initBlock base Init₁).PreambleSPSafe :=
  ⟨loopFree_initBlock base hInit₁.1,
    assignedAtMostOnce_initBlock base hInit₁.2⟩

/- Top-level loop containment distributes over list append. -/
private theorem containsTopLevelWhile_append
    {Ω : UnnamedSchema A}
    (Cs Ds : List (Cmd D Ω)) :
    Cmd.ContainsTopLevelWhile (Cs ++ Ds) ↔
      Cmd.ContainsTopLevelWhile Cs ∨
        Cmd.ContainsTopLevelWhile Ds := by
  induction Cs with
  | nil =>
      simp [Cmd.ContainsTopLevelWhile]
  | cons C Cs ih =>
      cases C <;> simp [Cmd.ContainsTopLevelWhile, ih]

/- Loop-free commands have no top-level while after
  flattening. -/
private theorem not_containsTopLevelWhile_flattenSeq_of_loopFree
    {Ω : UnnamedSchema A}
    {C : Cmd D Ω}
    (hC : C.LoopFree) :
    ¬ Cmd.ContainsTopLevelWhile C.flattenSeq := by
  induction C with
  | skip =>
      simp [Cmd.flattenSeq, Cmd.ContainsTopLevelWhile]
  | assign X e =>
      simp [Cmd.flattenSeq, Cmd.ContainsTopLevelWhile]
  | seq C₁ C₂ ih₁ ih₂ =>
      rw [Cmd.flattenSeq, containsTopLevelWhile_append]
      rintro (hLeft | hRight)
      · exact ih₁ hC.1 hLeft
      · exact ih₂ hC.2 hRight
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [Cmd.flattenSeq, Cmd.ContainsTopLevelWhile]
  | «while» G C ih =>
      exact False.elim hC

/- A flattened list with exactly one top-level loop is split
  into its preamble, loop, and close lists. -/
private theorem splitFramedLoopList?_single_loop
    {Ω : UnnamedSchema A}
    (Init Close : List (Cmd D Ω))
    (G : Guard D Ω)
    (Body : Cmd D Ω)
    (hInit : ¬ Cmd.ContainsTopLevelWhile Init)
    (hClose : ¬ Cmd.ContainsTopLevelWhile Close) :
    Cmd.splitFramedLoopList?
        (Init ++ (.while G Body :: Close)) =
      some (Init, G, Body, Close) := by
  induction Init with
  | nil =>
      simp [Cmd.splitFramedLoopList?, hClose]
  | cons C Init ih =>
      cases C with
      | skip =>
          have hTail :
              ¬ Cmd.ContainsTopLevelWhile Init := by
            intro h
            exact hInit
              (by
                simpa [Cmd.ContainsTopLevelWhile] using h)
          simp [Cmd.splitFramedLoopList?, ih hTail]
      | assign X e =>
          have hTail :
              ¬ Cmd.ContainsTopLevelWhile Init := by
            intro h
            exact hInit
              (by
                simpa [Cmd.ContainsTopLevelWhile] using h)
          simp [Cmd.splitFramedLoopList?, ih hTail]
      | seq C₁ C₂ =>
          have hTail :
              ¬ Cmd.ContainsTopLevelWhile Init := by
            intro h
            exact hInit
              (by
                simpa [Cmd.ContainsTopLevelWhile] using h)
          simp [Cmd.splitFramedLoopList?, ih hTail]
      | ite G₀ C₁ C₂ =>
          have hTail :
              ¬ Cmd.ContainsTopLevelWhile Init := by
            intro h
            exact hInit
              (by
                simpa [Cmd.ContainsTopLevelWhile] using h)
          simp [Cmd.splitFramedLoopList?, ih hTail]
      | «while» G₀ Body₀ =>
          exfalso
          exact hInit (by simp [Cmd.ContainsTopLevelWhile])

/- The generated command has the expected flattened
  one-loop shape. -/
private theorem flattenSeq_commandOfParts
    (base : A)
    (Init₁ : Cmd D Γ)
    (G₁ : Guard D Γ)
    (Body₁ Close₁ : Cmd D Γ)
    (Init₂ : Cmd D Γ)
    (G₂ : Guard D Γ)
    (Body₂ Close₂ : Cmd D Γ) :
    (commandOfParts
      base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
      Close₂).flattenSeq =
      (initBlock base Init₁).flattenSeq ++
        (.while
          (loopGuard (D := D) base Γ)
          (loopBody base G₁ Body₁ Close₁ Init₂ G₂
            Body₂) ::
          (liftCmd base Γ Close₂).flattenSeq) := by
  simp [commandOfParts, Cmd.framedLoopCommand,
    Cmd.flattenSeq, List.append_assoc]

/- The explicit flattened command is recognized as a
  framed loop. -/
theorem commandOfParts_framedLoop
    (base : A)
    {Init₁ Body₁ Close₁ Init₂ Body₂ Close₂ : Cmd D Γ}
    {G₁ G₂ : Guard D Γ}
    (hInit₁ : Init₁.PreambleSPSafe)
    (hBody₁ : Body₁.LoopFree)
    (hClose₁ : Close₁.LoopFree)
    (hInit₂ : Init₂.PreambleSPSafe)
    (hBody₂ : Body₂.LoopFree)
    (hClose₂ : Close₂.LoopFree) :
    (commandOfParts
      base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
      Close₂).FramedLoop := by
  let Init :=
    Cmd.seqList (initBlock base Init₁).flattenSeq
  let G := loopGuard (D := D) base Γ
  let Body :=
    loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂
  let Close :=
    Cmd.seqList (liftCmd base Γ Close₂).flattenSeq
  unfold Cmd.FramedLoop
  refine ⟨Init, G, Body, Close, ?_⟩
  have hInitNoWhile :
      ¬ Cmd.ContainsTopLevelWhile
          (initBlock base Init₁).flattenSeq :=
    not_containsTopLevelWhile_flattenSeq_of_loopFree
      (loopFree_initBlock base hInit₁.1)
  have hCloseNoWhile :
      ¬ Cmd.ContainsTopLevelWhile
          (liftCmd base Γ Close₂).flattenSeq :=
    not_containsTopLevelWhile_flattenSeq_of_loopFree
      ((loopFree_liftCmd base Γ Close₂).mpr hClose₂)
  have hSplit :
      Cmd.splitFramedLoopList?
          ((initBlock base Init₁).flattenSeq ++
            (.while
              (loopGuard (D := D) base Γ)
              (loopBody base G₁ Body₁ Close₁ Init₂ G₂
                Body₂) ::
              (liftCmd base Γ Close₂).flattenSeq)) =
        some
          ((initBlock base Init₁).flattenSeq,
            loopGuard (D := D) base Γ,
            loopBody base G₁ Body₁ Close₁ Init₂ G₂
              Body₂,
            (liftCmd base Γ Close₂).flattenSeq) :=
    splitFramedLoopList?_single_loop
      (Init := (initBlock base Init₁).flattenSeq)
      (Close := (liftCmd base Γ Close₂).flattenSeq)
      (G := loopGuard (D := D) base Γ)
      (Body :=
        loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
      hInitNoWhile hCloseNoWhile
  have hFlat :=
    flattenSeq_commandOfParts
      base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
      Close₂
  have hInitSafe :
      (Cmd.seqList
        (initBlock base Init₁).flattenSeq).PreambleSPSafe :=
    preambleSPSafe_seqList_flattenSeq
      (initBlock_preambleSPSafe base hInit₁)
  have hBodySafe :
      (loopBody base G₁ Body₁ Close₁ Init₂ G₂
        Body₂).LoopFree :=
    loopFree_loopBody
      base G₁ hBody₁ hClose₁ hInit₂.1 G₂ hBody₂
  have hCloseSafe :
      (Cmd.seqList
        (liftCmd base Γ Close₂).flattenSeq).LoopFree :=
    loopFree_seqList_flattenSeq
      ((loopFree_liftCmd base Γ Close₂).mpr hClose₂)
  unfold Cmd.framedLoopParts?
  rw [hFlat, hSplit]
  simp [Init, G, Body, Close, hInitSafe, hBodySafe,
    hCloseSafe]

/- Explicit-parts flattening preserves observable program
  behavior. -/
theorem programOfParts_bigStep_iff
    (base : A)
    {Init₁ Body₁ Close₁ Init₂ Body₂ Close₂ : Cmd D Γ}
    {G₁ G₂ : Guard D Γ}
    (I K : Instance D Γ) :
    (programOfParts
      base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
      Close₂).BigStep I K ↔
      (Program.ofCmd
        (.seq
          (Cmd.framedLoopCommand
            Init₁ G₁ Body₁ Close₁)
          (Cmd.framedLoopCommand
            Init₂ G₂ Body₂ Close₂))).BigStep I K := by
  rw [Program.ofCmd_bigStep_iff]
  constructor
  · intro hFlat
    rcases hFlat with ⟨JΩ, hCmd, hObs⟩
    have hRedInit :
        Instance.reduct (execSchema_extension base Γ)
          ((programOfParts
            base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
            Close₂).initialInstance I) = I :=
      Program.reduct_initialInstance
        (programOfParts
          base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
          Close₂) I
    have hCmdNorm :
        Cmd.BigStep
          (Cmd.framedLoopCommand
            (initBlock base Init₁)
            (loopGuard (D := D) base Γ)
            (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
            (liftCmd base Γ Close₂))
          ((programOfParts
            base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂
            Close₂).initialInstance I)
          JΩ := by
      simpa [programOfParts, commandOfParts] using hCmd
    unfold Cmd.framedLoopCommand at hCmdNorm
    rw [Cmd.bigStep_seq_iff] at hCmdNorm
    rcases hCmdNorm with ⟨AfterLoop, hInitLoop, hCloseΩ⟩
    rw [Cmd.bigStep_seq_iff] at hInitLoop
    rcases hInitLoop with ⟨AfterInit, hInitΩ, hOuter⟩
    rcases
      initBlock_bigStep_phase₁_reverse
        (D := D) base hRedInit hInitΩ with
      ⟨I₁, hInit₁, hPhase₁⟩
    let M₂ : Instance D Γ :=
      Instance.reduct (execSchema_extension base Γ) AfterLoop
    have hDoneOuter :
        Done (D := D) base AfterLoop M₂ := by
      unfold Done
      refine ⟨rfl, ?_, ?_⟩
      · intro hP₁
        exact
          (while_final_not_guard hOuter)
            ((loopGuard_eval_iff
              (D := D) base Γ AfterLoop).mpr
              (Or.inl hP₁))
      · intro hP₂
        exact
          (while_final_not_guard hOuter)
            ((loopGuard_eval_iff
              (D := D) base Γ AfterLoop).mpr
              (Or.inr hP₂))
    rcases
      dispatcher_phase₁_reverse
        (D := D) base hPhase₁ hOuter hDoneOuter with
      ⟨J₁, L₁, M₁, hLoop₁, hClose₁, hInit₂,
        hLoop₂⟩
    have hObs' :
        Instance.reduct (execSchema_extension base Γ) JΩ =
          K := by
      simpa [programOfParts, Program.observe] using hObs
    have hClose₂ :
        Cmd.BigStep Close₂ M₂ K := by
      simpa [M₂, hObs'] using
        (liftCmd_bigStep_reduct
          (D := D) base Γ hCloseΩ)
    have hFirst :
        Cmd.BigStep
          (Cmd.framedLoopCommand
            Init₁ G₁ Body₁ Close₁) I L₁ := by
      unfold Cmd.framedLoopCommand
      exact
        Cmd.BigStep.seq
          (Cmd.BigStep.seq hInit₁ hLoop₁)
          hClose₁
    have hSecond :
        Cmd.BigStep
          (Cmd.framedLoopCommand
            Init₂ G₂ Body₂ Close₂) L₁ K := by
      unfold Cmd.framedLoopCommand
      exact
        Cmd.BigStep.seq
          (Cmd.BigStep.seq hInit₂ hLoop₂)
          hClose₂
    exact Cmd.BigStep.seq hFirst hSecond
  · intro hSrc
    rw [Cmd.bigStep_seq_iff] at hSrc
    rcases hSrc with ⟨L₁, hFirst, hSecond⟩
    unfold Cmd.framedLoopCommand at hFirst
    rw [Cmd.bigStep_seq_iff] at hFirst
    rcases hFirst with ⟨J₁, hInitLoop₁, hClose₁⟩
    rw [Cmd.bigStep_seq_iff] at hInitLoop₁
    rcases hInitLoop₁ with ⟨I₁, hInit₁, hLoop₁⟩
    unfold Cmd.framedLoopCommand at hSecond
    rw [Cmd.bigStep_seq_iff] at hSecond
    rcases hSecond with ⟨M₂, hInitLoop₂, hClose₂⟩
    rw [Cmd.bigStep_seq_iff] at hInitLoop₂
    rcases hInitLoop₂ with ⟨M₁, hInit₂, hLoop₂⟩
    let P :=
      programOfParts
        base Init₁ G₁ Body₁ Close₁ Init₂ G₂ Body₂ Close₂
    have hRedInit :
        Instance.reduct (execSchema_extension base Γ)
          (P.initialInstance I) = I :=
      Program.reduct_initialInstance P I
    rcases
      initBlock_bigStep_phase₁
        (D := D) base hRedInit hInit₁ with
      ⟨I₁Ω, hInitΩ, hPhase₁⟩
    rcases
      dispatcher_phase₁_forward
        (D := D) base hPhase₁ hLoop₁ hClose₁ hInit₂
        hLoop₂ with
      ⟨M₂Ω, hOuterΩ, hDone⟩
    rcases
      liftCmd_bigStep_lift
        (D := D) base Γ hDone.1 hClose₂ with
      ⟨KΩ, hCloseΩ, hKReduct⟩
    refine ⟨KΩ, ?_, ?_⟩
    · have hCmd :
          Cmd.BigStep
            (Cmd.framedLoopCommand
              (initBlock base Init₁)
              (loopGuard (D := D) base Γ)
              (loopBody base G₁ Body₁ Close₁ Init₂ G₂ Body₂)
              (liftCmd base Γ Close₂))
            (P.initialInstance I) KΩ := by
          unfold Cmd.framedLoopCommand
          exact
            Cmd.BigStep.seq
              (Cmd.BigStep.seq hInitΩ hOuterΩ)
              hCloseΩ
      simpa [P, programOfParts, commandOfParts] using hCmd
    · simpa [P, programOfParts, Program.observe] using hKReduct

/- Computed flattening preserves observable program
  behavior. -/
theorem flattenCommand?_sound
    {base : A}
    {C : Cmd D Γ}
    {P : Program D Γ Γ}
    {I K : Instance D Γ}
    (h : flattenCommand? base C = some P) :
    P.BigStep I K ↔ (Program.ofCmd C).BigStep I K := by
  cases C with
  | skip =>
      simp [flattenCommand?] at h
  | assign X e =>
      simp [flattenCommand?] at h
  | ite G C₁ C₂ =>
      simp [flattenCommand?] at h
  | «while» G C =>
      simp [flattenCommand?] at h
  | seq C₁ C₂ =>
      unfold flattenCommand? flattenSeq? at h
      generalize hParts₁ :
        C₁.framedLoopParts? = parts₁ at h
      generalize hParts₂ :
        C₂.framedLoopParts? = parts₂ at h
      cases parts₁ with
      | none =>
          simp [hParts₁] at h
      | some p₁ =>
          rcases p₁ with ⟨Init₁, G₁, Body₁, Close₁⟩
          cases parts₂ with
          | none =>
              simp [hParts₁, hParts₂] at h
          | some p₂ =>
              rcases p₂ with
                ⟨Init₂, G₂, Body₂, Close₂⟩
              have hP :
                  programOfParts
                      base Init₁ G₁ Body₁ Close₁ Init₂ G₂
                      Body₂ Close₂ =
                    P := by
                have hSome :
                    some
                        (programOfParts
                          base Init₁ G₁ Body₁ Close₁ Init₂ G₂
                          Body₂ Close₂) =
                      some P := by
                  simpa [flattenCommand?, flattenSeq?,
                    hParts₁, hParts₂] using h
                injection hSome
              cases hP
              have hSound₁ :=
                Cmd.framedLoopParts?_sound hParts₁
              have hSound₂ :=
                Cmd.framedLoopParts?_sound hParts₂
              rw [programOfParts_bigStep_iff]
              rw [Program.ofCmd_bigStep_iff]
              rw [Program.ofCmd_bigStep_iff]
              constructor
              · intro hStep
                rw [Cmd.bigStep_seq_iff] at hStep
                rcases hStep with ⟨M, h₁, h₂⟩
                rw [Cmd.bigStep_seq_iff]
                exact
                  ⟨M,
                    (hSound₁.2.2.2 I M).mpr h₁,
                    (hSound₂.2.2.2 M K).mpr h₂⟩
              · intro hStep
                rw [Cmd.bigStep_seq_iff] at hStep
                rcases hStep with ⟨M, h₁, h₂⟩
                rw [Cmd.bigStep_seq_iff]
                exact
                  ⟨M,
                    (hSound₁.2.2.2 I M).mp h₁,
                    (hSound₂.2.2.2 M K).mp h₂⟩

end TwoLoopFlat

end Whiel
