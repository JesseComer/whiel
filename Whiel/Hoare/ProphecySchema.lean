-- Author: Jesse Comer
import Whiel.Concrete.WhielNames
import Whiel.Hoare.FixedAmbientProphecy
import Whiel.Hoare.Preproc
import Whiel.Hoare.PreprocSymbols

/-
  The computed prophecy schema and the input-boundary lift.

  A production input is a Hoare triple over one
  `UnnamedSchema ProgramNames`. Framework II works over the
  prophecy schema computed from that input schema and the
  assigned relations of the preprocessed loop body: the
  ordinary copy of every input relation plus a prophecy copy
  of every assigned one, at the input arity.

  The preprocessed loop triple is lifted by renaming at the
  raw-expression level and recomputing well-formedness, so no
  arity is ever transported. One transfer theorem returns
  prophecy-schema validity of the lifted loop to input-schema
  validity of the original loop.

  Key definitions include:
    * `Hoare.prophecySchema`
    * `Hoare.LoopTriple.lift`
    * `Hoare.liftedTask`
    * `Hoare.preprocess`

  Correctness is proven by:
    * `Hoare.LoopTriple.hoareValid_of_lift`
-/

------------------------------------------------------------
-- Computed Prophecy Schema
------------------------------------------------------------

namespace Whiel
namespace Hoare

open Concrete

/-
  Ordinary copy of every input relation plus a prophecy copy
  of every assigned one.
-/
def prophecySyms
    (Gamma : UnnamedSchema ProgramNames)
    (assigned : Finset ProgramNames) : Finset WhielNames :=
  Gamma.syms.image WhielNames.ordinary ∪
    (Gamma.syms.filter (· ∈ assigned)).image
      WhielNames.prophecy

theorem programName_mem_of_mem_prophecySyms
    {Gamma : UnnamedSchema ProgramNames}
    {assigned : Finset ProgramNames}
    {name : WhielNames}
    (h : name ∈ prophecySyms Gamma assigned) :
    name.programName ∈ Gamma.syms := by
  unfold prophecySyms at h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_image.mp h with ⟨X, hX, rfl⟩
    exact hX
  · rcases Finset.mem_image.mp h with ⟨X, hX, rfl⟩
    exact (Finset.mem_filter.mp hX).1

/-
  Arity is the input arity of the underlying program name;
  the equation is definitional, never transported.
-/
def prophecySchema
    (Gamma : UnnamedSchema ProgramNames)
    (assigned : Finset ProgramNames) :
    UnnamedSchema WhielNames where
  syms := prophecySyms Gamma assigned
  arity := fun r =>
    Gamma.arity
      ⟨r.1.programName,
        programName_mem_of_mem_prophecySyms r.2⟩

variable {Gamma : UnnamedSchema ProgramNames}
variable {assigned : Finset ProgramNames}

theorem ordinary_mem_prophecySchema
    {X : ProgramNames} (hX : X ∈ Gamma.syms) :
    WhielNames.ordinary X ∈
      (prophecySchema Gamma assigned).syms :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hX)

theorem mem_of_ordinary_mem_prophecySchema
    {X : ProgramNames}
    (h : WhielNames.ordinary X ∈
      (prophecySchema Gamma assigned).syms) :
    X ∈ Gamma.syms :=
  programName_mem_of_mem_prophecySyms h

theorem prophecy_mem_prophecySchema
    {X : ProgramNames} (hX : X ∈ Gamma.syms)
    (hAssigned : X ∈ assigned) :
    WhielNames.prophecy X ∈
      (prophecySchema Gamma assigned).syms :=
  Finset.mem_union_right _
    (Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨hX, hAssigned⟩))

theorem mem_prophecySchema_iff
    (name : WhielNames) :
    name ∈ (prophecySchema Gamma assigned).syms ↔
      (∃ X ∈ Gamma.syms, name = .ordinary X) ∨
        (∃ X ∈ Gamma.syms, X ∈ assigned ∧
          name = .prophecy X) := by
  unfold prophecySchema prophecySyms
  simp only [Finset.mem_union, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro (⟨X, hX, rfl⟩ | ⟨X, ⟨hX, hA⟩, rfl⟩)
    · exact Or.inl ⟨X, hX, rfl⟩
    · exact Or.inr ⟨X, hX, hA, rfl⟩
  · rintro (⟨X, hX, rfl⟩ | ⟨X, hX, hA, rfl⟩)
    · exact Or.inl ⟨X, hX, rfl⟩
    · exact Or.inr ⟨X, ⟨hX, hA⟩, rfl⟩

/- Every ordinary copy is a program symbol. -/
theorem ordinary_mem_programSymbols
    {X : ProgramNames} (hX : X ∈ Gamma.syms) :
    WhielNames.ordinary X ∈
      (prophecySchema Gamma assigned).programSymbols :=
  UnnamedSchema.mem_programSymbols.mpr
    ⟨ordinary_mem_prophecySchema hX, trivial⟩

end Hoare
end Whiel

------------------------------------------------------------
-- Raw-Level Lifting
------------------------------------------------------------

namespace Whiel
namespace Hoare

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema ProgramNames}
variable {assigned : Finset ProgramNames}

/- Rename every relation to its ordinary copy. -/
def mapNames :
    RawRAExpr ProgramNames D -> RawRAExpr WhielNames D
| .top => .top
| .empty n => .empty n
| .rel X => .rel (.ordinary X)
| .single d => .single d
| .select φ e => .select φ (mapNames e)
| .proj idxs e => .proj idxs (mapNames e)
| .prod e₁ e₂ => .prod (mapNames e₁) (mapNames e₂)
| .union e₁ e₂ => .union (mapNames e₁) (mapNames e₂)
| .diff e₁ e₂ => .diff (mapNames e₁) (mapNames e₂)

theorem arity?_ordinary (X : ProgramNames) :
    (prophecySchema Gamma assigned).arity?
        (WhielNames.ordinary X) =
      Gamma.arity? X := by
  unfold UnnamedSchema.arity?
  by_cases hX : X ∈ Gamma.syms
  · rw [dif_pos (ordinary_mem_prophecySchema hX),
      dif_pos hX]
    rfl
  · rw [dif_neg
      (fun h => hX (mem_of_ordinary_mem_prophecySchema h)),
      dif_neg hX]

theorem arity?_mapNames (e : RawRAExpr ProgramNames D) :
    (mapNames e).arity? (prophecySchema Gamma assigned) =
      e.arity? Gamma := by
  induction e with
  | top => rfl
  | empty n => rfl
  | rel X => exact arity?_ordinary X
  | single d => rfl
  | select φ e ih => simp only [mapNames, RawRAExpr.arity?, ih]
  | proj idxs e ih => simp only [mapNames, RawRAExpr.arity?, ih]
  | prod e₁ e₂ ih₁ ih₂ =>
      simp only [mapNames, RawRAExpr.arity?, ih₁, ih₂]
  | union e₁ e₂ ih₁ ih₂ =>
      simp only [mapNames, RawRAExpr.arity?, ih₁, ih₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [mapNames, RawRAExpr.arity?, ih₁, ih₂]

theorem symbols_mapNames (e : RawRAExpr ProgramNames D) :
    (mapNames e).symbols = e.symbols.image WhielNames.ordinary := by
  induction e with
  | top => simp [mapNames, RawRAExpr.symbols]
  | empty n => simp [mapNames, RawRAExpr.symbols]
  | rel X => simp [mapNames, RawRAExpr.symbols]
  | single d => simp [mapNames, RawRAExpr.symbols]
  | select φ e ih => simp [mapNames, RawRAExpr.symbols, ih]
  | proj idxs e ih => simp [mapNames, RawRAExpr.symbols, ih]
  | prod e₁ e₂ ih₁ ih₂ =>
      simp [mapNames, RawRAExpr.symbols, ih₁, ih₂,
        Finset.image_union]
  | union e₁ e₂ ih₁ ih₂ =>
      simp [mapNames, RawRAExpr.symbols, ih₁, ih₂,
        Finset.image_union]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp [mapNames, RawRAExpr.symbols, ih₁, ih₂,
        Finset.image_union]

/- Typed lift: the arity index is untouched; only the
  well-formedness proof is recomputed. -/
def liftRA {n : Nat} (e : RAExpr D Gamma n) :
    RAExpr D (prophecySchema Gamma assigned) n :=
  ⟨mapNames e.expr, by rw [arity?_mapNames]; exact e.wf⟩

def liftGuard :
    Guard D Gamma -> Guard D (prophecySchema Gamma assigned)
| .«true» => .«true»
| .«false» => .«false»
| .eq e₁ e₂ => .eq (liftRA e₁) (liftRA e₂)
| .subset e₁ e₂ => .subset (liftRA e₁) (liftRA e₂)
| .and φ ψ => .and (liftGuard φ) (liftGuard ψ)
| .or φ ψ => .or (liftGuard φ) (liftGuard ψ)
| .not φ => .not (liftGuard φ)

/- The assignment target's arity reduces definitionally. -/
def liftCmd :
    Cmd D Gamma -> Cmd D (prophecySchema Gamma assigned)
| .skip => .skip
| .assign X e =>
    .assign
      ⟨WhielNames.ordinary X.1,
        ordinary_mem_prophecySchema X.2⟩
      (liftRA e)
| .seq C₁ C₂ => .seq (liftCmd C₁) (liftCmd C₂)
| .ite G C₁ C₂ =>
    .ite (liftGuard G) (liftCmd C₁) (liftCmd C₂)
| .while G C => .while (liftGuard G) (liftCmd C)

theorem symbols_liftGuard (G : Guard D Gamma) :
    (liftGuard (assigned := assigned) G).symbols =
      G.symbols.image WhielNames.ordinary := by
  induction G with
  | «true» => simp [liftGuard, Guard.symbols]
  | «false» => simp [liftGuard, Guard.symbols]
  | eq e₁ e₂ =>
      simp [liftGuard, Guard.symbols, liftRA, RAExpr.symbols,
        symbols_mapNames, Finset.image_union]
  | subset e₁ e₂ =>
      simp [liftGuard, Guard.symbols, liftRA, RAExpr.symbols,
        symbols_mapNames, Finset.image_union]
  | and φ ψ ihφ ihψ =>
      simp [liftGuard, Guard.symbols, ihφ, ihψ,
        Finset.image_union]
  | or φ ψ ihφ ihψ =>
      simp [liftGuard, Guard.symbols, ihφ, ihψ,
        Finset.image_union]
  | not φ ih => simp [liftGuard, Guard.symbols, ih]

theorem symbols_liftCmd (C : Cmd D Gamma) :
    (liftCmd (assigned := assigned) C).symbols =
      C.symbols.image WhielNames.ordinary := by
  induction C with
  | skip => simp [liftCmd, Cmd.symbols]
  | assign X e =>
      simp [liftCmd, Cmd.symbols, liftRA, RAExpr.symbols,
        symbols_mapNames]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [liftCmd, Cmd.symbols, ih₁, ih₂, Finset.image_union]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [liftCmd, Cmd.symbols, ih₁, ih₂, symbols_liftGuard,
        Finset.image_union]
  | «while» G C ih =>
      simp [liftCmd, Cmd.symbols, ih, symbols_liftGuard,
        Finset.image_union]

theorem assignedSymbols_liftCmd (C : Cmd D Gamma) :
    (liftCmd (assigned := assigned) C).assignedSymbols =
      C.assignedSymbols.image WhielNames.ordinary := by
  induction C with
  | skip => simp [liftCmd, Cmd.assignedSymbols]
  | assign X e => simp [liftCmd, Cmd.assignedSymbols]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [liftCmd, Cmd.assignedSymbols, ih₁, ih₂,
        Finset.image_union]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [liftCmd, Cmd.assignedSymbols, ih₁, ih₂,
        Finset.image_union]
  | «while» G C ih => simp [liftCmd, Cmd.assignedSymbols, ih]

theorem liftCmd_loopFree
    {C : Cmd D Gamma} (h : C.LoopFree) :
    (liftCmd (assigned := assigned) C).LoopFree := by
  induction C with
  | skip => trivial
  | assign X e => trivial
  | seq C₁ C₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | ite G C₁ C₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | «while» G C ih => exact h.elim

/- Lifted symbols are program symbols of the prophecy schema. -/
theorem symbols_liftGuard_subset_programSymbols
    (G : Guard D Gamma) :
    (liftGuard (assigned := assigned) G).symbols ⊆
      (prophecySchema Gamma assigned).programSymbols := by
  rw [symbols_liftGuard]
  intro name hName
  rcases Finset.mem_image.mp hName with ⟨X, hX, rfl⟩
  exact ordinary_mem_programSymbols
    (Guard.symbols_subset_syms G hX)

theorem symbols_liftCmd_subset_programSymbols
    (C : Cmd D Gamma) :
    (liftCmd (assigned := assigned) C).symbols ⊆
      (prophecySchema Gamma assigned).programSymbols := by
  rw [symbols_liftCmd]
  intro name hName
  rcases Finset.mem_image.mp hName with ⟨X, hX, rfl⟩
  exact ordinary_mem_programSymbols
    (Cmd.symbols_subset_syms C hX)

end Hoare
end Whiel

------------------------------------------------------------
-- Instance Reduct, Extension, And Transfer
------------------------------------------------------------

namespace Whiel
namespace Hoare

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema ProgramNames}
variable {assigned : Finset ProgramNames}

/- The ordinary part of a prophecy-schema instance. -/
def reduct (J : Instance D (prophecySchema Gamma assigned)) :
    Instance D Gamma :=
  fun X => J ⟨WhielNames.ordinary X.1,
    ordinary_mem_prophecySchema X.2⟩

/- Extend an input instance with empty prophecy rows. -/
def extend (I : Instance D Gamma) :
    Instance D (prophecySchema Gamma assigned) :=
  fun r =>
    match r with
    | ⟨.ordinary X, h⟩ =>
        I ⟨X, mem_of_ordinary_mem_prophecySchema h⟩
    | ⟨.prophecy _, _⟩ => ∅

theorem reduct_extend (I : Instance D Gamma) :
    reduct (assigned := assigned) (extend I) = I := by
  funext X
  rfl

theorem relation?_ordinary
    (J : Instance D (prophecySchema Gamma assigned))
    (X : ProgramNames) :
    J.relation? (WhielNames.ordinary X) =
      (reduct J).relation? X := by
  unfold Instance.relation?
  by_cases hX : X ∈ Gamma.syms
  · rw [dif_pos (ordinary_mem_prophecySchema hX), dif_pos hX]
    rfl
  · rw [dif_neg
      (fun h => hX (mem_of_ordinary_mem_prophecySchema h)),
      dif_neg hX]

theorem eval?_mapNames (e : RawRAExpr ProgramNames D)
    (J : Instance D (prophecySchema Gamma assigned)) :
    (mapNames e).eval? J = e.eval? (reduct J) := by
  induction e with
  | top => rfl
  | empty n => rfl
  | rel X => exact relation?_ordinary J X
  | single d => rfl
  | select φ e ih => simp only [mapNames, RawRAExpr.eval?, ih]
  | proj idxs e ih => simp only [mapNames, RawRAExpr.eval?, ih]
  | prod e₁ e₂ ih₁ ih₂ =>
      simp only [mapNames, RawRAExpr.eval?, ih₁, ih₂]
  | union e₁ e₂ ih₁ ih₂ =>
      simp only [mapNames, RawRAExpr.eval?, ih₁, ih₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [mapNames, RawRAExpr.eval?, ih₁, ih₂]

theorem eval_liftRA {n : Nat} (e : RAExpr D Gamma n)
    (J : Instance D (prophecySchema Gamma assigned)) :
    (liftRA e).eval J = e.eval (reduct J) := by
  unfold RAExpr.eval liftRA
  simp only [eval?_mapNames]

theorem eval_liftGuard (G : Guard D Gamma)
    (J : Instance D (prophecySchema Gamma assigned)) :
    (liftGuard G).eval J ↔ G.eval (reduct J) := by
  induction G with
  | «true» => exact Iff.rfl
  | «false» => exact Iff.rfl
  | eq e₁ e₂ => simp only [liftGuard, Guard.eval, eval_liftRA]
  | subset e₁ e₂ =>
      simp only [liftGuard, Guard.eval, eval_liftRA]
  | and φ ψ ihφ ihψ => simp only [liftGuard, Guard.eval, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [liftGuard, Guard.eval, ihφ, ihψ]
  | not φ ih => simp only [liftGuard, Guard.eval, ih]

theorem extend_update (I : Instance D Gamma) (X : Gamma.syms)
    (R : FinRelation D (Gamma.arity X)) :
    extend (assigned := assigned) (Instance.update I X R) =
      Instance.update (extend I)
        ⟨WhielNames.ordinary X.1,
          ordinary_mem_prophecySchema X.2⟩ R := by
  funext r
  rcases r with ⟨name, h⟩
  cases name with
  | ordinary Y =>
      by_cases hY : Y = X.1
      · have hEq : (⟨WhielNames.ordinary Y, h⟩ :
            (prophecySchema Gamma assigned).syms) =
            ⟨WhielNames.ordinary X.1,
              ordinary_mem_prophecySchema X.2⟩ :=
          Subtype.ext (by simp [hY])
        rw [hEq, Instance.update_lookup_eq]
        change Instance.update I X R X = R
        exact Instance.update_lookup_eq I X R
      · have hNe : (⟨WhielNames.ordinary Y, h⟩ :
            (prophecySchema Gamma assigned).syms) ≠
            ⟨WhielNames.ordinary X.1,
              ordinary_mem_prophecySchema X.2⟩ := by
          intro hEq
          apply hY
          have := congrArg Subtype.val hEq
          simpa using this
        rw [Instance.update_lookup_ne _ _ _ hNe]
        change Instance.update I X R ⟨Y, _⟩ = I ⟨Y, _⟩
        have hNeY :
            (⟨Y, mem_of_ordinary_mem_prophecySchema h⟩ :
              Gamma.syms) ≠ X := by
          intro hEq
          exact hY (congrArg Subtype.val hEq)
        rw [Instance.update_lookup_ne _ _ _ hNeY]
  | prophecy Y =>
      have hNe : (⟨WhielNames.prophecy Y, h⟩ :
          (prophecySchema Gamma assigned).syms) ≠
          ⟨WhielNames.ordinary X.1,
            ordinary_mem_prophecySchema X.2⟩ := by
        intro hEq
        have := congrArg Subtype.val hEq
        simp at this
      rw [Instance.update_lookup_ne _ _ _ hNe]
      rfl

theorem bigStep_lift {C : Cmd D Gamma} {I I' : Instance D Gamma}
    (h : Cmd.BigStep C I I') :
    Cmd.BigStep (liftCmd (assigned := assigned) C)
      (extend I) (extend I') := by
  induction h with
  | skip I => exact Cmd.BigStep.skip _
  | assign I X e =>
      rw [extend_update]
      have hEval : e.eval I =
          (liftRA (assigned := assigned) e).eval (extend I) := by
        rw [eval_liftRA, reduct_extend]
      rw [hEval]
      exact Cmd.BigStep.assign _ _ _
  | seq _ _ ih₁ ih₂ => exact Cmd.BigStep.seq ih₁ ih₂
  | ite_true hG _ ih =>
      exact Cmd.BigStep.ite_true
        ((eval_liftGuard _ _).mpr
          (by rw [reduct_extend]; exact hG)) ih
  | ite_false hG _ ih =>
      exact Cmd.BigStep.ite_false
        (fun hLift => hG (by
          have := (eval_liftGuard _ _).mp hLift
          rwa [reduct_extend] at this)) ih
  | while_false hG =>
      exact Cmd.BigStep.while_false
        (fun hLift => hG (by
          have := (eval_liftGuard _ _).mp hLift
          rwa [reduct_extend] at this))
  | while_true hG _ _ ih₁ ih₂ =>
      exact Cmd.BigStep.while_true
        ((eval_liftGuard _ _).mpr
          (by rw [reduct_extend]; exact hG))
        ih₁ ih₂

end Hoare
end Whiel

------------------------------------------------------------
-- Loop Triples And The Lifted Task
------------------------------------------------------------

namespace Whiel
namespace Hoare

open Concrete

variable {D : Type} [Domain D]

/-
  One loop-only triple: the quantifier-free precondition,
  guard, loop-free body, and quantifier-free postcondition
  Framework II certifies.
-/
structure LoopTriple
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Gamma : UnnamedSchema A) where
  pre : QFAssertExpr D Gamma
  guard : Guard D Gamma
  body : Cmd D Gamma
  body_loopFree : body.LoopFree
  post : QFAssertExpr D Gamma

namespace LoopTriple

variable {A : Type} [RelationNames A]

/- Hoare validity of the loop-only triple. -/
def Valid
    {Gamma : UnnamedSchema A}
    (loop : LoopTriple D Gamma) : Prop :=
  HoareValid loop.pre.eval (.while loop.guard loop.body)
    loop.post.eval

/-
  The preprocessed loop of an input triple, over the flag
  extension the preprocessor drew.
-/
def ofPreproc
    {Gamma : UnnamedSchema A}
    {inputPre inputPost : AssertExpr D Gamma}
    {inputCmd : Cmd D Gamma}
    (P : Preproc inputPre inputCmd inputPost) :
    LoopTriple D P.outSchema where
  pre := P.loopPre.toQFOfNoBound P.loopPre_noBound
  guard := P.loopGuard
  body := P.loopBody
  body_loopFree := P.loopBody_loopFree
  post := P.loopPost.toQFOfNoBound P.loopPost_noBound

/- A valid preprocessed loop proves the input triple. -/
theorem valid_input_of_ofPreproc
    {Gamma : UnnamedSchema A}
    {inputPre inputPost : AssertExpr D Gamma}
    {inputCmd : Cmd D Gamma}
    (P : Preproc inputPre inputCmd inputPost)
    (hLoop : (ofPreproc P).Valid) :
    HoareValid inputPre inputCmd inputPost := by
  apply P.valid_input
  intro initial final hPre hRun
  apply (AssertExpr.toQFOfNoBound_eval_iff
    P.loopPost P.loopPost_noBound final).mp
  apply hLoop initial final
  · exact (AssertExpr.toQFOfNoBound_eval_iff
      P.loopPre P.loopPre_noBound initial).mpr hPre
  · exact hRun

variable {Gamma : UnnamedSchema ProgramNames}

/- The prophecy schema of one input loop. -/
def prophecySchema (loop : LoopTriple D Gamma) :
    UnnamedSchema WhielNames :=
  Hoare.prophecySchema Gamma loop.body.assignedSymbols

/- Lift the loop to its prophecy schema. -/
def lift (loop : LoopTriple D Gamma) :
    LoopTriple D loop.prophecySchema where
  pre := liftGuard loop.pre
  guard := liftGuard loop.guard
  body := liftCmd loop.body
  body_loopFree := liftCmd_loopFree loop.body_loopFree
  post := liftGuard loop.post

/-
  The transfer theorem: prophecy-schema validity of the lifted
  loop pulls back to input-schema validity of the loop.
-/
theorem hoareValid_of_lift
    (loop : LoopTriple D Gamma)
    (hLift : loop.lift.Valid) : loop.Valid := by
  intro I I' hPre hStep
  have hPost := hLift (extend I) (extend I')
    ((eval_liftGuard loop.pre _).mpr
      (by rw [reduct_extend]; exact hPre))
    (bigStep_lift hStep)
  have := (eval_liftGuard loop.post _).mp hPost
  rwa [reduct_extend] at this

end LoopTriple

/-
  The three correspondence facts of a lifted loop body, proved
  once: every assignment is ordinary, has a prophecy row, and
  agrees in arity. No input file constructs a task value.
-/
def liftedTask
    {Gamma : UnnamedSchema ProgramNames}
    (C : Cmd D Gamma) :
    WhielNamesProphecy.Task
      (liftCmd (assigned := C.assignedSymbols) C) where
  assignedOrdinary := by
    intro name h
    rw [assignedSymbols_liftCmd] at h
    rcases Finset.mem_image.mp h with ⟨X, _, rfl⟩
    trivial
  prophecyMem := by
    intro X h
    rw [assignedSymbols_liftCmd] at h
    rcases Finset.mem_image.mp h with ⟨Y, hY, hEq⟩
    cases hEq
    exact prophecy_mem_prophecySchema
      (Cmd.assignedSymbols_subset_syms C hY) hY
  prophecyArity := by
    intro X h
    rfl

/- The lifted loop's task. -/
def LoopTriple.task
    {Gamma : UnnamedSchema ProgramNames}
    (loop : LoopTriple D Gamma) :
    WhielNamesProphecy.Task loop.lift.body :=
  liftedTask loop.body

namespace LoopTriple

variable {A : Type} [RelationNames A]
variable {Gamma : UnnamedSchema A}

/- The loop command of a loop triple. -/
def cmd (loop : LoopTriple D Gamma) : Cmd D Gamma :=
  .while loop.guard loop.body

/- The precondition as a bound-symbol-free assertion. -/
def preAssert (loop : LoopTriple D Gamma) : AssertExpr D Gamma :=
  AssertExpr.ofQF loop.pre

theorem preAssert_noBound (loop : LoopTriple D Gamma) :
    loop.preAssert.NoBoundSymbols :=
  AssertExpr.ofQF_noBound loop.pre

/- The postcondition as a bound-symbol-free assertion. -/
def postAssert (loop : LoopTriple D Gamma) : AssertExpr D Gamma :=
  AssertExpr.ofQF loop.post

theorem postAssert_noBound (loop : LoopTriple D Gamma) :
    loop.postAssert.NoBoundSymbols :=
  AssertExpr.ofQF_noBound loop.post

end LoopTriple

namespace Preproc

variable {Gamma : UnnamedSchema ProgramNames}
variable {inputPre inputPost : AssertExpr D Gamma}
variable {inputCmd : Cmd D Gamma}

/- The prophecy schema computed from one preprocessed input. -/
def prophecySchema
    (P : Preproc inputPre inputCmd inputPost) :
    UnnamedSchema WhielNames :=
  (LoopTriple.ofPreproc P).prophecySchema

/- The preprocessed loop lifted to its prophecy schema. -/
def liftedLoop
    (P : Preproc inputPre inputCmd inputPost) :
    LoopTriple D P.prophecySchema :=
  (LoopTriple.ofPreproc P).lift

end Preproc

end Hoare
end Whiel

------------------------------------------------------------
-- Production Input Preprocessing
------------------------------------------------------------

namespace Whiel
namespace Hoare

open Concrete

variable {D : Type} [Domain D]

/-
  Production preprocessing of one raw input triple: the
  generic preprocessor of `Whiel/Preprocess/**`, taken
  through the bridge of `Hoare.ofPreprocessed`.

  The input command is arbitrary. What the entry point still
  decides for the input file is that both stated assertions
  are quantifier-free, which is what the retagging of the
  precondition and the closing weakest precondition of the
  postcondition need, so an input file declares nothing but
  its five values. The flag supply is seeded inside the
  transformation from the input schema itself, so no
  index-zero discipline is imposed on the schema any more.
-/
def preprocess
    {Gamma : UnnamedSchema ProgramNames}
    (inputPre : AssertExpr D Gamma)
    (inputCmd : Cmd D Gamma)
    (inputPost : AssertExpr D Gamma)
    (hNoPre : inputPre.NoBoundSymbols := by decide)
    (hNoPost : inputPost.NoBoundSymbols := by decide) :
    Preproc inputPre inputCmd inputPost :=
  ofPreprocessed inputPre inputCmd inputPost hNoPre hNoPost

/- The production entry point is the generic preprocessor. -/
theorem preprocess_eq_ofPreprocessed
    {Gamma : UnnamedSchema ProgramNames}
    (inputPre : AssertExpr D Gamma)
    (inputCmd : Cmd D Gamma)
    (inputPost : AssertExpr D Gamma)
    (hNoPre : inputPre.NoBoundSymbols)
    (hNoPost : inputPost.NoBoundSymbols) :
    preprocess inputPre inputCmd inputPost hNoPre hNoPost =
      ofPreprocessed inputPre inputCmd inputPost hNoPre
        hNoPost :=
  rfl

/-
  The preprocessed loop is the framed loop the generic
  preprocessor returns, over the flag extension it drew.
-/
theorem preprocess_outSchema
    {Gamma : UnnamedSchema ProgramNames}
    (inputPre : AssertExpr D Gamma)
    (inputCmd : Cmd D Gamma)
    (inputPost : AssertExpr D Gamma)
    (hNoPre : inputPre.NoBoundSymbols)
    (hNoPost : inputPost.NoBoundSymbols) :
    (preprocess inputPre inputCmd inputPost hNoPre
        hNoPost).outSchema =
      Preprocess.flagExt Gamma
        (Preprocess.preprocess inputCmd inputPre
          hNoPre).ids :=
  rfl

end Hoare
end Whiel
