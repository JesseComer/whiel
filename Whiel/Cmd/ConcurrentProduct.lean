-- Author: Jesse Comer
import Whiel.Cmd.Rewrites.TwoLoopFlat

/-
  Certified lockstep products of independent Whiel programs.

  Key definitions include:
    * `Whiel.ConcurrentProduct.Component`
    * `Whiel.ConcurrentProduct.Independent`
    * `Whiel.ConcurrentProduct.product`

  The product construction merges two execution schemas and
  builds one loop whose guard is the disjunction of the
    local
  guards and whose body unconditionally sequences both local
  bodies.  Shared footprint symbols are read-only.

  Correctness is expressed by:
    * `Whiel.ConcurrentProduct.product_bigStep_iff`
    * `Whiel.ConcurrentProduct.product_bigStep_sound`
    * `Whiel.ConcurrentProduct.product_bigStep_complete`

  The general command-retagging lemmas imported from
  `TwoLoopFlat` are reused, but no phase symbols or phased
  execution machinery participate in this construction.
-/

------------------------------------------------------------
-- Schema Merging
------------------------------------------------------------

namespace Whiel

namespace ConcurrentProduct

variable {A : Type} [RelationNames A]

/- Compatibility of arities on shared schema symbols. -/
def ArityCompatible
    (Γ Δ : UnnamedSchema A) : Prop :=
  Γ.agreeOnArities (Γ.syms ∩ Δ.syms) Δ

instance instDecidableArityCompatible
    (Γ Δ : UnnamedSchema A) :
    Decidable (ArityCompatible Γ Δ) := by
  unfold ArityCompatible
  infer_instance

/- Left-biased union of arity-compatible schemas. -/
def mergeSchema
    (Γ Δ : UnnamedSchema A)
    (_hAr : ArityCompatible Γ Δ) :
    UnnamedSchema A where
  syms := Γ.syms ∪ Δ.syms
  arity := fun X =>
    if hX : X.1 ∈ Γ.syms then
      Γ.arity ⟨X.1, hX⟩
    else
      Δ.arity
        ⟨X.1, by
          have hMem := Finset.mem_union.mp X.2
          exact hMem.resolve_left hX⟩

/- The merged schema extends its left operand. -/
theorem mergeSchema_extension_left
    (Γ Δ : UnnamedSchema A)
    (hAr : ArityCompatible Γ Δ) :
    (mergeSchema Γ Δ hAr).extensionOf Γ := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact Finset.mem_union_left Δ.syms hX
  · intro X
    simp [mergeSchema, UnnamedSchema.arity?, X.2]

/- The merged schema extends its right operand. -/
theorem mergeSchema_extension_right
    (Γ Δ : UnnamedSchema A)
    (hAr : ArityCompatible Γ Δ) :
    (mergeSchema Γ Δ hAr).extensionOf Δ := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact Finset.mem_union_right Γ.syms hX
  · intro X
    by_cases hXΓ : X.1 ∈ Γ.syms
    · have hAgree := hAr X.1 (by simp [hXΓ, X.2])
      unfold UnnamedSchema.arity? at hAgree
      simp [hXΓ, X.2] at hAgree
      simp [mergeSchema, UnnamedSchema.arity?, hXΓ,
        X.2, hAgree]
    · simp [mergeSchema, UnnamedSchema.arity?, hXΓ,
        X.2]

end ConcurrentProduct

end Whiel


------------------------------------------------------------
-- Certified Loop Components
------------------------------------------------------------

namespace Whiel

namespace ConcurrentProduct

variable {A D : Type}
variable [RelationNames A] [Domain D]

/- A certified single-loop program component. -/
structure Component where
  inputSchema : UnnamedSchema A
  outputSchema : UnnamedSchema A
  program : Program D inputSchema outputSchema
  init : Cmd D program.execSchema
  guard : Guard D program.execSchema
  body : Cmd D program.execSchema
  close : Cmd D program.execSchema
  footprint : Finset A
  footprint_subset : footprint ⊆ program.execSchema.syms
  input_subset : inputSchema.syms ⊆ footprint
  output_subset : outputSchema.syms ⊆ footprint
  init_symbols : init.symbols ⊆ footprint
  guard_symbols : guard.symbols ⊆ footprint
  body_symbols : body.symbols ⊆ footprint
  close_symbols : close.symbols ⊆ footprint
  init_loopFree : init.LoopFree
  body_loopFree : body.LoopFree
  close_loopFree : close.LoopFree
  invariant : Instance D program.execSchema → Prop
  invariant_local :
    ∀ {I J : Instance D program.execSchema},
      Instance.agreeOn footprint I J →
        (invariant I ↔ invariant J)
  init_invariant :
    ∀ (I : Instance D inputSchema)
      {J : Instance D program.execSchema},
      Cmd.BigStep init (program.initialInstance I) J →
        invariant J
  body_invariant :
    ∀ {I J : Instance D program.execSchema},
      invariant I → Cmd.BigStep body I J → invariant J
  body_stutter :
    ∀ {I : Instance D program.execSchema},
      invariant I → ¬ guard.eval I →
        Cmd.BigStep body I I
  cmd_equiv :
    Cmd.BigStepEquiv program.cmd
      (Cmd.framedLoopCommand init guard body close)

namespace Component

private theorem assigned_subset_symbols
    {Γ : UnnamedSchema A}
    (C : Cmd D Γ) :
    C.assignedSymbols ⊆ C.symbols := by
  induction C with
  | skip => simp [Cmd.assignedSymbols, Cmd.symbols]
  | assign X e => simp [Cmd.assignedSymbols, Cmd.symbols]
  | seq C₁ C₂ ih₁ ih₂ =>
      simpa [Cmd.assignedSymbols, Cmd.symbols] using
        Finset.union_subset_union ih₁ ih₂
  | ite G C₁ C₂ ih₁ ih₂ =>
      intro X hX
      simp only [Cmd.assignedSymbols,
        Finset.mem_union] at hX
      simp only [Cmd.symbols, Finset.mem_union]
      rcases hX with hX | hX
      · exact Or.inl (Or.inr (ih₁ hX))
      · exact Or.inr (ih₂ hX)
  | «while» G C ih =>
      intro X hX
      simp only [Cmd.assignedSymbols] at hX
      simp only [Cmd.symbols, Finset.mem_union]
      exact Or.inr (ih hX)

/- Symbols assigned by a component's executable parts. -/
def writes
    (C : Component (A := A) (D := D)) : Finset A :=
  C.init.assignedSymbols ∪
    C.body.assignedSymbols ∪
      C.close.assignedSymbols

/- Every component write lies in its footprint. -/
theorem writes_subset
    (C : Component (A := A) (D := D)) :
    C.writes ⊆ C.footprint := by
  intro X hX
  rcases Finset.mem_union.mp hX with hInitBody | hClose
  · rcases Finset.mem_union.mp hInitBody with hInit | hBody
    · exact C.init_symbols
        (assigned_subset_symbols C.init hInit)
    · exact C.body_symbols
        (assigned_subset_symbols C.body hBody)
  · exact C.close_symbols
      (assigned_subset_symbols C.close hClose)

/- Initialization assignments are component writes. -/
theorem init_assigned_subset_writes
    (C : Component (A := A) (D := D)) :
    C.init.assignedSymbols ⊆ C.writes := by
  intro X hX
  simp [writes, hX]

/- Body assignments are component writes. -/
theorem body_assigned_subset_writes
    (C : Component (A := A) (D := D)) :
    C.body.assignedSymbols ⊆ C.writes := by
  intro X hX
  simp [writes, hX]

/- Closing assignments are component writes. -/
theorem close_assigned_subset_writes
    (C : Component (A := A) (D := D)) :
    C.close.assignedSymbols ⊆ C.writes := by
  intro X hX
  simp [writes, hX]

/- Build a component from recognized framed-loop parts. -/
def ofFramedLoopParts
    {Δ Λ : UnnamedSchema A}
    (P : Program D Δ Λ)
    (Init : Cmd D P.execSchema)
    (G : Guard D P.execSchema)
    (Body Close : Cmd D P.execSchema)
    (hParts :
      P.cmd.framedLoopParts? =
        some (Init, G, Body, Close))
    (footprint : Finset A)
    (hFootprint : footprint ⊆ P.execSchema.syms)
    (hInput : Δ.syms ⊆ footprint)
    (hOutput : Λ.syms ⊆ footprint)
    (hInitSymbols : Init.symbols ⊆ footprint)
    (hGuardSymbols : G.symbols ⊆ footprint)
    (hBodySymbols : Body.symbols ⊆ footprint)
    (hCloseSymbols : Close.symbols ⊆ footprint)
    (Inv : Instance D P.execSchema → Prop)
    (hLocal :
      ∀ {I J : Instance D P.execSchema},
        Instance.agreeOn footprint I J →
          (Inv I ↔ Inv J))
    (hInitInv :
      ∀ (I : Instance D Δ)
        {J : Instance D P.execSchema},
        Cmd.BigStep Init (P.initialInstance I) J → Inv J)
    (hBodyInv :
      ∀ {I J : Instance D P.execSchema},
        Inv I → Cmd.BigStep Body I J → Inv J)
    (hStutter :
      ∀ {I : Instance D P.execSchema},
        Inv I → ¬ G.eval I → Cmd.BigStep Body I I) :
    Component (A := A) (D := D) where
  inputSchema := Δ
  outputSchema := Λ
  program := P
  init := Init
  guard := G
  body := Body
  close := Close
  footprint := footprint
  footprint_subset := hFootprint
  input_subset := hInput
  output_subset := hOutput
  init_symbols := hInitSymbols
  guard_symbols := hGuardSymbols
  body_symbols := hBodySymbols
  close_symbols := hCloseSymbols
  init_loopFree :=
    (Cmd.framedLoopParts?_sound hParts).1.1
  body_loopFree :=
    (Cmd.framedLoopParts?_sound hParts).2.1
  close_loopFree :=
    (Cmd.framedLoopParts?_sound hParts).2.2.1
  invariant := Inv
  invariant_local := hLocal
  init_invariant := hInitInv
  body_invariant := hBodyInv
  body_stutter := hStutter
  cmd_equiv :=
    fun I J =>
      (Cmd.framedLoopParts?_sound hParts).2.2.2 I J

end Component

end ConcurrentProduct

end Whiel

------------------------------------------------------------
-- Independence And Product Schemas
------------------------------------------------------------

namespace Whiel

namespace ConcurrentProduct

variable {A D : Type}
variable [RelationNames A] [Domain D]

/- Static independence conditions for two components. -/
structure Independent
    (C₁ C₂ : Component (A := A) (D := D)) : Prop where
  arityCompatible :
    ArityCompatible
      C₁.program.execSchema C₂.program.execSchema
  leftWrites : C₁.writes ∩ C₂.footprint = ∅
  rightWrites : C₂.writes ∩ C₁.footprint = ∅
  leftWritesExec :
    C₁.writes ∩ C₂.program.execSchema.syms = ∅
  rightWritesExec :
    C₂.writes ∩ C₁.program.execSchema.syms = ∅
  leftInputs :
    C₂.inputSchema.syms ∩ C₁.footprint ⊆
      C₁.inputSchema.syms
  rightInputs :
    C₁.inputSchema.syms ∩ C₂.footprint ⊆
      C₂.inputSchema.syms
  leftExecInputs :
    C₂.inputSchema.syms ∩ C₁.program.execSchema.syms
      ⊆
      C₁.inputSchema.syms
  rightExecInputs :
    C₁.inputSchema.syms ∩ C₂.program.execSchema.syms
      ⊆
      C₂.inputSchema.syms

namespace Independent

/- Independence implies disjoint component writes. -/
theorem disjoint_writes
    {C₁ C₂ : Component (A := A) (D := D)}
    (h : Independent C₁ C₂) :
    C₁.writes ∩ C₂.writes = ∅ := by
  apply Finset.Subset.antisymm
  · intro X hX
    have hPair := Finset.mem_inter.mp hX
    have hFoot : X ∈ C₂.footprint :=
      C₂.writes_subset hPair.2
    have hBad : X ∈ C₁.writes ∩ C₂.footprint :=
      Finset.mem_inter.mpr ⟨hPair.1, hFoot⟩
    have : False := by
      rw [h.leftWrites] at hBad
      simp at hBad
    exact False.elim this
  · exact Finset.empty_subset _

end Independent

variable
  (C₁ C₂ : Component (A := A) (D := D))
  (hInd : Independent C₁ C₂)

/- Execution schema of the concurrent product. -/
def productExecSchema : UnnamedSchema A :=
  mergeSchema C₁.program.execSchema
    C₂.program.execSchema
    hInd.arityCompatible

/- Product execution schema extends the left schema. -/
theorem productExecSchema_extension_left :
    (productExecSchema C₁ C₂ hInd).extensionOf
      C₁.program.execSchema :=
  mergeSchema_extension_left _ _ hInd.arityCompatible

/- Product execution schema extends the right schema. -/
theorem productExecSchema_extension_right :
    (productExecSchema C₁ C₂ hInd).extensionOf
      C₂.program.execSchema :=
  mergeSchema_extension_right _ _ hInd.arityCompatible

private theorem input_union_subset_exec :
    C₁.inputSchema.syms ∪ C₂.inputSchema.syms ⊆
      (productExecSchema C₁ C₂ hInd).syms := by
  intro X hX
  rcases Finset.mem_union.mp hX with hX | hX
  · exact (productExecSchema_extension_left C₁ C₂
    hInd).1
      (C₁.program.extendsInput.1 hX)
  · exact (productExecSchema_extension_right C₁ C₂
    hInd).1
      (C₂.program.extendsInput.1 hX)

private theorem output_union_subset_exec :
    C₁.outputSchema.syms ∪ C₂.outputSchema.syms ⊆
      (productExecSchema C₁ C₂ hInd).syms := by
  intro X hX
  rcases Finset.mem_union.mp hX with hX | hX
  · exact (productExecSchema_extension_left C₁ C₂
    hInd).1
      (C₁.program.extendsOutput.1 hX)
  · exact (productExecSchema_extension_right C₁ C₂
    hInd).1
      (C₂.program.extendsOutput.1 hX)

/- External input schema of the product. -/
def productInputSchema : UnnamedSchema A :=
  UnnamedSchema.restrict
    (productExecSchema C₁ C₂ hInd)
    (C₁.inputSchema.syms ∪ C₂.inputSchema.syms)
    (input_union_subset_exec C₁ C₂ hInd)

/- Observable output schema of the product. -/
def productOutputSchema : UnnamedSchema A :=
  UnnamedSchema.restrict
    (productExecSchema C₁ C₂ hInd)
    (C₁.outputSchema.syms ∪ C₂.outputSchema.syms)
    (output_union_subset_exec C₁ C₂ hInd)

/- Product execution extends the product input. -/
theorem productExecSchema_extension_input :
    (productExecSchema C₁ C₂ hInd).extensionOf
      (productInputSchema C₁ C₂ hInd) :=
  UnnamedSchema.extensionOf_restrict _ _ _

/- Product execution extends the product output. -/
theorem productExecSchema_extension_output :
    (productExecSchema C₁ C₂ hInd).extensionOf
      (productOutputSchema C₁ C₂ hInd) :=
  UnnamedSchema.extensionOf_restrict _ _ _

/- Product input extends the left input schema. -/
theorem productInputSchema_extension_left :
    (productInputSchema C₁ C₂ hInd).extensionOf
      C₁.inputSchema := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact Finset.mem_union_left _ hX
  · intro X
    let Y : C₁.program.execSchema.syms :=
      UnnamedSchema.symOfExtension
        C₁.program.extendsInput X
    have hExt :=
      UnnamedSchema.arity_eq_of_extensionOf
        (productExecSchema_extension_left C₁ C₂ hInd)
        Y
    have hInput :=
      UnnamedSchema.arity_eq_of_extensionOf
        C₁.program.extendsInput X
    unfold productInputSchema UnnamedSchema.restrict
      UnnamedSchema.arity?
    simpa [Y, UnnamedSchema.symOfExtension] using
      hExt.trans hInput

/- Product input extends the right input schema. -/
theorem productInputSchema_extension_right :
    (productInputSchema C₁ C₂ hInd).extensionOf
      C₂.inputSchema := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact Finset.mem_union_right _ hX
  · intro X
    let Y : C₂.program.execSchema.syms :=
      UnnamedSchema.symOfExtension
        C₂.program.extendsInput X
    have hExt :=
      UnnamedSchema.arity_eq_of_extensionOf
        (productExecSchema_extension_right C₁ C₂ hInd)
        Y
    have hInput :=
      UnnamedSchema.arity_eq_of_extensionOf
        C₂.program.extendsInput X
    unfold productInputSchema UnnamedSchema.restrict
      UnnamedSchema.arity?
    simpa [Y, UnnamedSchema.symOfExtension] using
      hExt.trans hInput

/- Product output extends the left output schema. -/
theorem productOutputSchema_extension_left :
    (productOutputSchema C₁ C₂ hInd).extensionOf
      C₁.outputSchema := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact Finset.mem_union_left _ hX
  · intro X
    let Y : C₁.program.execSchema.syms :=
      UnnamedSchema.symOfExtension
        C₁.program.extendsOutput X
    have hExt :=
      UnnamedSchema.arity_eq_of_extensionOf
        (productExecSchema_extension_left C₁ C₂ hInd)
        Y
    have hOutput :=
      UnnamedSchema.arity_eq_of_extensionOf
        C₁.program.extendsOutput X
    unfold productOutputSchema UnnamedSchema.restrict
      UnnamedSchema.arity?
    simpa [Y, UnnamedSchema.symOfExtension] using
      hExt.trans hOutput

/- Product output extends the right output schema. -/
theorem productOutputSchema_extension_right :
    (productOutputSchema C₁ C₂ hInd).extensionOf
      C₂.outputSchema := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact Finset.mem_union_right _ hX
  · intro X
    let Y : C₂.program.execSchema.syms :=
      UnnamedSchema.symOfExtension
        C₂.program.extendsOutput X
    have hExt :=
      UnnamedSchema.arity_eq_of_extensionOf
        (productExecSchema_extension_right C₁ C₂ hInd)
        Y
    have hOutput :=
      UnnamedSchema.arity_eq_of_extensionOf
        C₂.program.extendsOutput X
    unfold productOutputSchema UnnamedSchema.restrict
      UnnamedSchema.arity?
    simpa [Y, UnnamedSchema.symOfExtension] using
      hExt.trans hOutput

end ConcurrentProduct

end Whiel

------------------------------------------------------------
-- Concurrent Product Construction
------------------------------------------------------------

namespace Whiel

namespace ConcurrentProduct

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable
  (C₁ C₂ : Component (A := A) (D := D))
  (hInd : Independent C₁ C₂)

/- Lift the left initialization into the product schema. -/
def leftInit : Cmd D (productExecSchema C₁ C₂ hInd) :=
  C₁.init.onExtension
    (productExecSchema_extension_left C₁ C₂ hInd)

/- Lift the right initialization into the product schema. -/
def rightInit : Cmd D (productExecSchema C₁ C₂ hInd) :=
  C₂.init.onExtension
    (productExecSchema_extension_right C₁ C₂ hInd)

/- Lift the left loop guard into the product schema. -/
def leftGuard : Guard D (productExecSchema C₁ C₂ hInd)
  :=
  C₁.guard.onExtension
    (productExecSchema_extension_left C₁ C₂ hInd)

/- Lift the right loop guard into the product schema. -/
def rightGuard : Guard D (productExecSchema C₁ C₂ hInd)
  :=
  C₂.guard.onExtension
    (productExecSchema_extension_right C₁ C₂ hInd)

/- Lift the left loop body into the product schema. -/
def leftBody : Cmd D (productExecSchema C₁ C₂ hInd) :=
  C₁.body.onExtension
    (productExecSchema_extension_left C₁ C₂ hInd)

/- Lift the right loop body into the product schema. -/
def rightBody : Cmd D (productExecSchema C₁ C₂ hInd) :=
  C₂.body.onExtension
    (productExecSchema_extension_right C₁ C₂ hInd)

/- Lift the left closing block into the product schema. -/
def leftClose : Cmd D (productExecSchema C₁ C₂ hInd) :=
  C₁.close.onExtension
    (productExecSchema_extension_left C₁ C₂ hInd)

/- Lift the right closing block into the product schema. -/
def rightClose : Cmd D (productExecSchema C₁ C₂ hInd) :=
  C₂.close.onExtension
    (productExecSchema_extension_right C₁ C₂ hInd)

/- Both initializations, in their fixed source order. -/
def productInit : Cmd D (productExecSchema C₁ C₂ hInd)
  :=
  .seq (leftInit C₁ C₂ hInd) (rightInit C₁ C₂ hInd)

/- Disjunction of the local continuation guards. -/
def productGuard : Guard D (productExecSchema C₁ C₂
  hInd) :=
  .or (leftGuard C₁ C₂ hInd) (rightGuard C₁ C₂ hInd)

/- Both bodies execute on every global iteration. -/
def productBody : Cmd D (productExecSchema C₁ C₂ hInd)
  :=
  .seq (leftBody C₁ C₂ hInd) (rightBody C₁ C₂ hInd)

/- Both closing blocks, in their fixed source order. -/
def productClose : Cmd D (productExecSchema C₁ C₂ hInd)
  :=
  .seq (leftClose C₁ C₂ hInd) (rightClose C₁ C₂
    hInd)

/- The single-loop concurrent product command. -/
def productCommand : Cmd D (productExecSchema C₁ C₂
  hInd) :=
  Cmd.framedLoopCommand
    (productInit C₁ C₂ hInd)
    (productGuard C₁ C₂ hInd)
    (productBody C₁ C₂ hInd)
    (productClose C₁ C₂ hInd)

/- The program underlying the concurrent product. -/
def productProgram :
    Program D
      (productInputSchema C₁ C₂ hInd)
      (productOutputSchema C₁ C₂ hInd) where
  execSchema := productExecSchema C₁ C₂ hInd
  extendsInput :=
    productExecSchema_extension_input C₁ C₂ hInd
  extendsOutput :=
    productExecSchema_extension_output C₁ C₂ hInd
  cmd := productCommand C₁ C₂ hInd

/- The product command has exactly the advertised shape. -/
theorem productCommand_eq :
    productCommand C₁ C₂ hInd =
      Cmd.framedLoopCommand
        (.seq (leftInit C₁ C₂ hInd)
          (rightInit C₁ C₂ hInd))
        (.or (leftGuard C₁ C₂ hInd)
          (rightGuard C₁ C₂ hInd))
        (.seq (leftBody C₁ C₂ hInd)
          (rightBody C₁ C₂ hInd))
        (.seq (leftClose C₁ C₂ hInd)
          (rightClose C₁ C₂ hInd)) := by
  rfl

/- Product assignments are exactly the union of writes. -/
@[simp] theorem assignedSymbols_productCommand :
    (productCommand C₁ C₂ hInd).assignedSymbols =
      C₁.writes ∪ C₂.writes := by
  simp [productCommand, Cmd.framedLoopCommand,
    productInit, productBody, productClose,
    leftInit, rightInit, leftBody, rightBody,
    leftClose, rightClose, Component.writes,
    Cmd.assignedSymbols, Finset.union_assoc,
    Finset.union_left_comm]

end ConcurrentProduct

end Whiel

------------------------------------------------------------
-- Lifted Execution Support
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/- Number of syntactic while commands. -/
def whileCount : Cmd D Γ → Nat
| .skip => 0
| .assign _ _ => 0
| .seq C₁ C₂ => C₁.whileCount + C₂.whileCount
| .ite _ C₁ C₂ => C₁.whileCount + C₂.whileCount
| .while _ C => 1 + C.whileCount

/- Loop-free commands contain no while commands. -/
theorem whileCount_eq_zero_of_loopFree
    {C : Cmd D Γ}
    (hFree : C.LoopFree) :
    C.whileCount = 0 := by
  induction C with
  | skip =>
      rfl
  | assign X e =>
      rfl
  | seq C₁ C₂ ih₁ ih₂ =>
      exact Nat.add_eq_zero_iff.mpr
        ⟨ih₁ hFree.1, ih₂ hFree.2⟩
  | ite G C₁ C₂ ih₁ ih₂ =>
      exact Nat.add_eq_zero_iff.mpr
        ⟨ih₁ hFree.1, ih₂ hFree.2⟩
  | «while» G C ih =>
      contradiction

/- Assigned names belong to the command's schema. -/
theorem assignedSymbols_subset_schema
    (C : Cmd D Γ) :
    C.assignedSymbols ⊆ Γ.syms := by
  induction C with
  | skip => simp [assignedSymbols]
  | assign X e => simp [assignedSymbols, X.2]
  | seq C₁ C₂ ih₁ ih₂ =>
      simpa [assignedSymbols] using
        Finset.union_subset ih₁ ih₂
  | ite G C₁ C₂ ih₁ ih₂ =>
      simpa [assignedSymbols] using
        Finset.union_subset ih₁ ih₂
  | «while» G C ih => simpa [assignedSymbols] using ih

/- A stuttering source run lifts to an exact ambient
  stutter. -/
theorem onExtension_bigStep_stutter
    (hExt : Ω.extensionOf Γ)
    {C : Cmd D Γ}
    {I : Instance D Γ}
    {IΩ : Instance D Ω}
    (hReduct : Instance.reduct hExt IΩ = I)
    (hStep : BigStep C I I) :
    BigStep (C.onExtension hExt) IΩ IΩ := by
  rcases onExtension_bigStep_lift hExt hReduct hStep with
    ⟨JΩ, hLift, hJReduct⟩
  have hIExt : Instance.Extends hExt I IΩ :=
    Instance.extends_of_reduct_eq hExt hReduct
  have hJExt : Instance.Extends hExt I JΩ :=
    Instance.extends_of_reduct_eq hExt hJReduct
  have hEq : JΩ = IΩ := by
    apply Instance.ext
    intro X
    by_cases hX : X.1 ∈ Γ.syms
    · exact (hJExt X hX).trans (hIExt X hX).symm
    · exact hLift.no_update_preservation X (by
        intro hWrite
        have hOld : X.1 ∈ C.assignedSymbols := by
          simpa [Cmd.assignedSymbols_onExtension] using
            hWrite
        have hIn : X.1 ∈ Γ.syms :=
          assignedSymbols_subset_schema C hOld
        exact hX hIn)
  simpa [hEq] using hLift

/- A lifted run preserves a disjoint ambient reduct. -/
theorem onExtension_preserves_reduct
    {Δ : UnnamedSchema A}
    (hΓ : Ω.extensionOf Γ)
    (hΔ : Ω.extensionOf Δ)
    {C : Cmd D Γ}
    {I J : Instance D Ω}
    (hDis : C.assignedSymbols ∩ Δ.syms = ∅)
    (hStep : BigStep (C.onExtension hΓ) I J) :
    Instance.reduct hΔ J = Instance.reduct hΔ I := by
  apply Instance.ext
  intro X
  unfold Instance.reduct
  rw [hStep.no_update_preservation]
  intro hWrite
  have hOld : X.1 ∈ C.assignedSymbols := by
    simpa [Cmd.assignedSymbols_onExtension] using hWrite
  have hBad : X.1 ∈ C.assignedSymbols ∩ Δ.syms := by
    exact Finset.mem_inter.mpr ⟨hOld, X.2⟩
  rw [hDis] at hBad
  simp at hBad

end Cmd

end Whiel

------------------------------------------------------------
-- Lockstep Loop Soundness
------------------------------------------------------------

namespace Whiel

namespace ConcurrentProduct

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable
  (C₁ C₂ : Component (A := A) (D := D))
  (hInd : Independent C₁ C₂)

private theorem left_body_disjoint_right
    (hInd : Independent C₁ C₂) :
    C₁.body.assignedSymbols ∩
        C₂.program.execSchema.syms = ∅ := by
  apply Finset.Subset.antisymm
  · intro X hX
    have hPair := Finset.mem_inter.mp hX
    have hBad : X ∈ C₁.writes ∩
        C₂.program.execSchema.syms :=
      Finset.mem_inter.mpr
        ⟨C₁.body_assigned_subset_writes hPair.1,
          hPair.2⟩
    have : False := by
      rw [Independent.leftWritesExec hInd] at hBad
      simp at hBad
    exact False.elim this
  · exact Finset.empty_subset _

private theorem right_body_disjoint_left
    (hInd : Independent C₁ C₂) :
    C₂.body.assignedSymbols ∩
        C₁.program.execSchema.syms = ∅ := by
  apply Finset.Subset.antisymm
  · intro X hX
    have hPair := Finset.mem_inter.mp hX
    have hBad : X ∈ C₂.writes ∩
        C₁.program.execSchema.syms :=
      Finset.mem_inter.mpr
        ⟨C₂.body_assigned_subset_writes hPair.1,
          hPair.2⟩
    have : False := by
      rw [Independent.rightWritesExec hInd] at hBad
      simp at hBad
    exact False.elim this
  · exact Finset.empty_subset _

private theorem leftGuard_eval_iff
    (I : Instance D (productExecSchema C₁ C₂ hInd)) :
    (leftGuard C₁ C₂ hInd).eval I ↔
      C₁.guard.eval
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          I) := by
  letI : Fact
      ((productExecSchema C₁ C₂ hInd).extensionOf
        C₁.program.execSchema) :=
    ⟨productExecSchema_extension_left C₁ C₂ hInd⟩
  exact Guard.onExtension_eval_reduct
    (Γ := productExecSchema C₁ C₂ hInd)
    (Δ := C₁.program.execSchema)
    C₁.guard I _ rfl

private theorem rightGuard_eval_iff
    (I : Instance D (productExecSchema C₁ C₂ hInd)) :
    (rightGuard C₁ C₂ hInd).eval I ↔
      C₂.guard.eval
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          I) := by
  letI : Fact
      ((productExecSchema C₁ C₂ hInd).extensionOf
        C₂.program.execSchema) :=
    ⟨productExecSchema_extension_right C₁ C₂ hInd⟩
  exact Guard.onExtension_eval_reduct
    (Γ := productExecSchema C₁ C₂ hInd)
    (Δ := C₂.program.execSchema)
    C₂.guard I _ rfl

private theorem productLoop_sound_aux
    {W : Cmd D (productExecSchema C₁ C₂ hInd)}
    {I J : Instance D (productExecSchema C₁ C₂ hInd)}
    (hStep : Cmd.BigStep W I J)
    (hW :
      (.while (productGuard C₁ C₂ hInd)
        (productBody C₁ C₂ hInd) :
          Cmd D (productExecSchema C₁ C₂ hInd)) = W)
    (hInv₁ :
      C₁.invariant
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          I))
    (hInv₂ :
      C₂.invariant
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          I))
    :
    Cmd.BigStep (.while C₁.guard C₁.body)
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            I)
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            J) ∧
      Cmd.BigStep (.while C₂.guard C₂.body)
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            I)
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            J) := by
  revert hW hInv₁ hInv₂
  induction hStep with
  | skip I => intro hW _ _; cases hW
  | assign I X e => intro hW _ _; cases hW
  | seq h₁ h₂ ih₁ ih₂ => intro hW _ _; cases hW
  | ite_true hG hC ih => intro hW _ _; cases hW
  | ite_false hG hC ih => intro hW _ _; cases hW
  | @while_false G Body I₀ hFalse =>
      intro hW hInv₁ hInv₂
      cases hW
      have hNotLeft :
          ¬ (leftGuard C₁ C₂ hInd).eval I₀ := by
        intro hEval
        apply hFalse
        exact Or.inl hEval
      have hNotRight :
          ¬ (rightGuard C₁ C₂ hInd).eval I₀ := by
        intro hEval
        apply hFalse
        exact Or.inr hEval
      exact
        ⟨Cmd.BigStep.while_false
            (fun h => hNotLeft
              ((leftGuard_eval_iff C₁ C₂ hInd I₀).mpr
                h)),
          Cmd.BigStep.while_false
            (fun h => hNotRight
              ((rightGuard_eval_iff C₁ C₂ hInd I₀).mpr
                h))⟩
  | @while_true G Body I₀ N J₀ hGuard hRound hLoop
      ihRound ihLoop =>
      intro hW hInv₁ hInv₂
      cases hW
      change Cmd.BigStep
        (.seq (leftBody C₁ C₂ hInd)
          (rightBody C₁ C₂ hInd)) _ _ at hRound
      rw [Cmd.bigStep_seq_iff] at hRound
      rcases hRound with ⟨M, hLeft, hRight⟩
      have hLeftLocal :=
        Cmd.onExtension_bigStep_reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          hLeft
      have hRightLocalM :=
        Cmd.onExtension_bigStep_reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          hRight
      have hRightPreservesLeft :
          Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd)
              _ =
            Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd)
              M :=
        Cmd.onExtension_preserves_reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          (productExecSchema_extension_left C₁ C₂ hInd)
          (right_body_disjoint_left C₁ C₂ hInd)
          hRight
      have hLeftPreservesRight :
          Instance.reduct
              (productExecSchema_extension_right C₁ C₂
                hInd)
              M =
            Instance.reduct
              (productExecSchema_extension_right C₁ C₂
                hInd)
              I₀ :=
        Cmd.onExtension_preserves_reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          (productExecSchema_extension_right C₁ C₂ hInd)
          (left_body_disjoint_right C₁ C₂ hInd)
          hLeft
      rw [hLeftPreservesRight] at hRightLocalM
      have hInvLeftM := C₁.body_invariant hInv₁
        hLeftLocal
      have hInvLeftNext :
          C₁.invariant
            (Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd)
              N) := by
        rw [hRightPreservesLeft]
        exact hInvLeftM
      have hInvRightNext :=
        C₂.body_invariant hInv₂ hRightLocalM
      have hRec := ihLoop rfl hInvLeftNext hInvRightNext
      constructor
      · by_cases hG₁ :
          C₁.guard.eval
            (Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd)
              I₀)
        · rw [hRightPreservesLeft] at hRec
          exact Cmd.BigStep.while_true hG₁ hLeftLocal
            hRec.1
        · have hStutter := C₁.body_stutter hInv₁ hG₁
          have hM :=
            Cmd.BigStep.deterministic hLeftLocal hStutter
          have hRest :
              Cmd.BigStep (.while C₁.guard C₁.body)
                (Instance.reduct
                  (productExecSchema_extension_left
                    C₁ C₂ hInd) I₀)
                (Instance.reduct
                  (productExecSchema_extension_left
                    C₁ C₂ hInd) J₀) := by
            rw [hRightPreservesLeft, hM] at hRec
            exact hRec.1
          have hFalseStep :
              Cmd.BigStep (.while C₁.guard C₁.body)
                (Instance.reduct
                  (productExecSchema_extension_left
                    C₁ C₂ hInd) I₀)
                (Instance.reduct
                  (productExecSchema_extension_left
                    C₁ C₂ hInd) I₀) :=
            Cmd.BigStep.while_false hG₁
          have hFinal :=
            Cmd.BigStep.deterministic hRest hFalseStep
          rw [hFinal]
          exact hFalseStep
      · by_cases hG₂ :
          C₂.guard.eval
            (Instance.reduct
              (productExecSchema_extension_right C₁ C₂
                hInd)
              I₀)
        · exact
            Cmd.BigStep.while_true hG₂ hRightLocalM hRec.2
        · have hStutter := C₂.body_stutter hInv₂ hG₂
          have hN :=
            Cmd.BigStep.deterministic hRightLocalM hStutter
          have hRest :
              Cmd.BigStep (.while C₂.guard C₂.body)
                (Instance.reduct
                  (productExecSchema_extension_right
                    C₁ C₂ hInd) I₀)
                (Instance.reduct
                  (productExecSchema_extension_right
                    C₁ C₂ hInd) J₀) := by
            rw [hN] at hRec
            exact hRec.2
          have hFalseStep :
              Cmd.BigStep (.while C₂.guard C₂.body)
                (Instance.reduct
                  (productExecSchema_extension_right
                    C₁ C₂ hInd) I₀)
                (Instance.reduct
                  (productExecSchema_extension_right
                    C₁ C₂ hInd) I₀) :=
            Cmd.BigStep.while_false hG₂
          have hFinal :=
            Cmd.BigStep.deterministic hRest hFalseStep
          rw [hFinal]
          exact hFalseStep

/- A global loop run projects to both source loop runs. -/
theorem productLoop_sound
    {I J : Instance D (productExecSchema C₁ C₂ hInd)}
    (hInv₁ :
      C₁.invariant
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          I))
    (hInv₂ :
      C₂.invariant
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          I))
    (hStep :
      Cmd.BigStep
        (.while (productGuard C₁ C₂ hInd)
          (productBody C₁ C₂ hInd)) I J) :
    Cmd.BigStep (.while C₁.guard C₁.body)
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            I)
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            J) ∧
      Cmd.BigStep (.while C₂.guard C₂.body)
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            I)
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            J) := by
  exact productLoop_sound_aux C₁ C₂ hInd hStep rfl
    hInv₁ hInv₂

end ConcurrentProduct

end Whiel

------------------------------------------------------------
-- Product Initial And Observable States
------------------------------------------------------------

namespace Whiel

namespace ConcurrentProduct

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable
  (C₁ C₂ : Component (A := A) (D := D))
  (hInd : Independent C₁ C₂)

/- Product initialization reduces to left initialization. -/
theorem reduct_product_initial_left
    (I : Instance D (productInputSchema C₁ C₂ hInd)) :
    Instance.reduct
        (productExecSchema_extension_left C₁ C₂ hInd)
        ((productProgram C₁ C₂ hInd).initialInstance I)
          =
      C₁.program.initialInstance
        (Instance.reduct
          (productInputSchema_extension_left C₁ C₂ hInd)
          I) := by
  apply Instance.ext
  intro X
  by_cases hX : X.1 ∈ C₁.inputSchema.syms
  · unfold Program.initialInstance Instance.reduct
      Instance.expandEmpty Instance.relationOfExtension
    simp [productProgram, productInputSchema,
      UnnamedSchema.restrict, hX]
  · have hNotOther : X.1 ∉ C₂.inputSchema.syms := by
      intro hOther
      apply hX
      exact hInd.leftExecInputs
        (Finset.mem_inter.mpr ⟨hOther, X.2⟩)
    unfold Program.initialInstance Instance.reduct
      Instance.expandEmpty
    simp only [productInputSchema, UnnamedSchema.restrict,
      Finset.mem_union, hX, hNotOther, or_self,
      ↓reduceDIte, productProgram]
    apply Finset.ext
    intro t
    let hAr :=
      UnnamedSchema.arity_eq_of_extensionOf
        (productExecSchema_extension_left C₁ C₂ hInd) X
    rw [FinRelation.mem_cast_iff hAr]
    constructor <;> intro hEmpty
    · exact False.elim
        (Finset.not_nonempty_empty ⟨_, hEmpty⟩)
    · exact False.elim
        (Finset.not_nonempty_empty ⟨_, hEmpty⟩)

/- Product initialization reduces to right initialization.
  -/
theorem reduct_product_initial_right
    (I : Instance D (productInputSchema C₁ C₂ hInd)) :
    Instance.reduct
        (productExecSchema_extension_right C₁ C₂ hInd)
        ((productProgram C₁ C₂ hInd).initialInstance I)
          =
      C₂.program.initialInstance
        (Instance.reduct
          (productInputSchema_extension_right C₁ C₂
            hInd)
          I) := by
  apply Instance.ext
  intro X
  by_cases hX : X.1 ∈ C₂.inputSchema.syms
  · unfold Program.initialInstance Instance.reduct
      Instance.expandEmpty Instance.relationOfExtension
    simp [productProgram, productInputSchema,
      UnnamedSchema.restrict, hX]
  · have hNotOther : X.1 ∉ C₁.inputSchema.syms := by
      intro hOther
      apply hX
      exact hInd.rightExecInputs
        (Finset.mem_inter.mpr ⟨hOther, X.2⟩)
    unfold Program.initialInstance Instance.reduct
      Instance.expandEmpty
    simp only [productInputSchema, UnnamedSchema.restrict,
      Finset.mem_union, hNotOther, hX, or_self,
      ↓reduceDIte, productProgram]
    apply Finset.ext
    intro t
    let hAr :=
      UnnamedSchema.arity_eq_of_extensionOf
        (productExecSchema_extension_right C₁ C₂ hInd) X
    rw [FinRelation.mem_cast_iff hAr]
    constructor <;> intro hEmpty
    · exact False.elim
        (Finset.not_nonempty_empty ⟨_, hEmpty⟩)
    · exact False.elim
        (Finset.not_nonempty_empty ⟨_, hEmpty⟩)

/- Observing then projecting left equals projecting first.
  -/
theorem reduct_product_observe_left
    (J : Instance D (productExecSchema C₁ C₂ hInd)) :
    Instance.reduct
        (productOutputSchema_extension_left C₁ C₂ hInd)
        ((productProgram C₁ C₂ hInd).observe J) =
      C₁.program.observe
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          J) := by
  unfold Program.observe productProgram
  apply Instance.ext
  intro X
  unfold Instance.reduct
  simp

/- Observing then projecting right equals projecting first.
  -/
theorem reduct_product_observe_right
    (J : Instance D (productExecSchema C₁ C₂ hInd)) :
    Instance.reduct
        (productOutputSchema_extension_right C₁ C₂ hInd)
        ((productProgram C₁ C₂ hInd).observe J) =
      C₂.program.observe
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          J) := by
  unfold Program.observe productProgram
  apply Instance.ext
  intro X
  unfold Instance.reduct
  simp

end ConcurrentProduct

end Whiel

------------------------------------------------------------
-- Instance Agreement Support
------------------------------------------------------------

namespace Instance

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Agreement on a union is componentwise agreement. -/
theorem agreeOn_union_iff
    (S T : Finset A)
    (I J : Instance D Γ) :
    agreeOn (S ∪ T) I J ↔
      agreeOn S I J ∧ agreeOn T I J := by
  constructor
  · intro h
    constructor
    · intro X hX
      exact h X (by simp [hX])
    · intro X hX
      exact h X (by simp [hX])
  · rintro ⟨hS, hT⟩ X hX
    rcases Finset.mem_union.mp hX with hXS | hXT
    · exact hS X hXS
    · exact hT X hXT

/- Agreement is reflexive. -/
theorem agreeOn_refl
    (S : Finset A)
    (I : Instance D Γ) :
    agreeOn S I I := by
  intro _ _
  rfl

/- Agreement is transitive. -/
theorem agreeOn_trans
    {S : Finset A}
    {I J K : Instance D Γ}
    (hIJ : agreeOn S I J)
    (hJK : agreeOn S J K) :
    agreeOn S I K := by
  intro X hX
  exact (hIJ X hX).trans (hJK X hX)

end Instance

------------------------------------------------------------
-- Command Framing
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A run agrees with its input on an unwritten set. -/
theorem BigStep.agreeOn_of_disjoint
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    (hStep : BigStep C I J)
    (S : Finset A)
    (hDis : C.assignedSymbols ∩ S = ∅) :
    Instance.agreeOn S I J := by
  intro X hX
  symm
  exact hStep.no_update_preservation X (by
    intro hWrite
    have : X.1 ∈ C.assignedSymbols ∩ S := by
      simp [hWrite, hX]
    rw [hDis] at this
    simp at this)

end Cmd

end Whiel

------------------------------------------------------------
-- Lockstep Loop Completeness
------------------------------------------------------------

namespace Whiel

namespace ConcurrentProduct

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable
  (C₁ C₂ : Component (A := A) (D := D))
  (hInd : Independent C₁ C₂)

private theorem productLoop_left_done_aux
    {W₂ : Cmd D C₂.program.execSchema}
    {I₂ J₂ : Instance D C₂.program.execSchema}
    (hRight : Cmd.BigStep W₂ I₂ J₂) :
    (.while C₂.guard C₂.body :
      Cmd D C₂.program.execSchema) = W₂ →
    ∀ {IΩ : Instance D (productExecSchema C₁ C₂
      hInd)},
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          IΩ = I₂ →
      C₁.invariant
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          IΩ) →
      C₂.invariant I₂ →
      (¬ C₁.guard.eval
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          IΩ)) →
      ∃ JΩ : Instance D (productExecSchema C₁ C₂
        hInd),
        Cmd.BigStep
          (.while (productGuard C₁ C₂ hInd)
            (productBody C₁ C₂ hInd)) IΩ JΩ ∧
        Instance.reduct
            (productExecSchema_extension_left C₁ C₂
              hInd)
            JΩ =
          Instance.reduct
            (productExecSchema_extension_left C₁ C₂
              hInd)
            IΩ ∧
        Instance.reduct
            (productExecSchema_extension_right C₁ C₂
              hInd)
            JΩ = J₂ := by
  induction hRight with
  | skip I => intro hW; cases hW
  | assign I X e => intro hW; cases hW
  | seq h₁ h₂ ih₁ ih₂ => intro hW; cases hW
  | ite_true hG hC ih => intro hW; cases hW
  | ite_false hG hC ih => intro hW; cases hW
  | @while_false G Body I hFalse =>
      intro hW IΩ hRed₂ hInv₁ hInv₂ hDone₁
      cases hW
      refine ⟨IΩ, ?_, rfl, hRed₂⟩
      apply Cmd.BigStep.while_false
      intro hProduct
      rcases hProduct with hLeft | hRight
      · exact hDone₁
          ((leftGuard_eval_iff C₁ C₂ hInd IΩ).mp hLeft)
      · exact hFalse
          (by
            rw [← hRed₂]
            exact
              (rightGuard_eval_iff C₁ C₂ hInd IΩ).mp
                hRight)
  | @while_true G Body I K J hG hBody hLoop
      ihBody ihLoop =>
      intro hW IΩ hRed₂ hInv₁ hInv₂ hDone₁
      cases hW
      have hLeftStutter := C₁.body_stutter hInv₁
        hDone₁
      have hLiftLeft :
          Cmd.BigStep (leftBody C₁ C₂ hInd) IΩ IΩ :=
        Cmd.onExtension_bigStep_stutter
          (productExecSchema_extension_left C₁ C₂ hInd)
          rfl hLeftStutter
      rcases
          Cmd.onExtension_bigStep_lift
            (productExecSchema_extension_right C₁ C₂
              hInd)
            hRed₂ hBody
        with ⟨KΩ, hLiftRight, hRedK⟩
      have hLeftK :
          Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd)
              KΩ =
            Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd)
              IΩ :=
        Cmd.onExtension_preserves_reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          (productExecSchema_extension_left C₁ C₂ hInd)
          (right_body_disjoint_left C₁ C₂ hInd)
          hLiftRight
      have hInv₂K := C₂.body_invariant hInv₂ hBody
      have hDone₁K :
          ¬ C₁.guard.eval
            (Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd)
              KΩ) := by
        rw [hLeftK]
        exact hDone₁
      have hInv₁K :
          C₁.invariant
            (Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd)
              KΩ) := by
        rw [hLeftK]
        exact hInv₁
      rcases ihLoop rfl (IΩ := KΩ) hRedK
          hInv₁K hInv₂K hDone₁K
        with ⟨JΩ, hRest, hFinal₁, hFinal₂⟩
      refine ⟨JΩ, ?_, ?_, hFinal₂⟩
      · apply Cmd.BigStep.while_true
        · exact Or.inr
            ((rightGuard_eval_iff C₁ C₂ hInd IΩ).mpr
              (by simpa [hRed₂] using hG))
        · exact Cmd.BigStep.seq hLiftLeft hLiftRight
        · exact hRest
      · exact hFinal₁.trans hLeftK

private theorem productLoop_complete_aux
    {W₁ : Cmd D C₁.program.execSchema}
    {I₁ J₁ : Instance D C₁.program.execSchema}
    (hLeft : Cmd.BigStep W₁ I₁ J₁) :
    (.while C₁.guard C₁.body :
      Cmd D C₁.program.execSchema) = W₁ →
    ∀ {IΩ : Instance D (productExecSchema C₁ C₂
      hInd)}
      {I₂ J₂ : Instance D C₂.program.execSchema},
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          IΩ = I₁ →
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          IΩ = I₂ →
      C₁.invariant I₁ → C₂.invariant I₂ →
      Cmd.BigStep (.while C₂.guard C₂.body) I₂ J₂
        →
      ∃ JΩ : Instance D (productExecSchema C₁ C₂
        hInd),
        Cmd.BigStep
          (.while (productGuard C₁ C₂ hInd)
            (productBody C₁ C₂ hInd)) IΩ JΩ ∧
        Instance.reduct
            (productExecSchema_extension_left C₁ C₂
              hInd)
            JΩ = J₁ ∧
        Instance.reduct
            (productExecSchema_extension_right C₁ C₂
              hInd)
            JΩ = J₂ := by
  induction hLeft with
  | skip I => intro hW; cases hW
  | assign I X e => intro hW; cases hW
  | seq h₁ h₂ ih₁ ih₂ => intro hW; cases hW
  | ite_true hG hC ih => intro hW; cases hW
  | ite_false hG hC ih => intro hW; cases hW
  | @while_false G Body I hFalse =>
      intro hW IΩ I₂ J₂ hRed₁ hRed₂ hInv₁ hInv₂
        hRight
      cases hW
      rcases
          productLoop_left_done_aux C₁ C₂ hInd hRight
            rfl
            hRed₂ (by simpa [hRed₁] using hInv₁)
              hInv₂
            (by simpa [hRed₁] using hFalse)
        with ⟨JΩ, hStep, hFinal₁, hFinal₂⟩
      exact ⟨JΩ, hStep, hFinal₁.trans hRed₁,
        hFinal₂⟩
  | @while_true G Body I K J hG hBody hLoop
      ihBody ihLoop =>
      intro hW IΩ I₂ J₂ hRed₁ hRed₂ hInv₁ hInv₂
        hRight
      cases hW
      rw [Cmd.bigStep_while_iff] at hRight
      rcases hRight with hRightDone | hRightStep
      · rcases hRightDone with ⟨hG₂, hEq₂⟩
        subst J₂
        rcases
            Cmd.onExtension_bigStep_lift
              (productExecSchema_extension_left C₁ C₂
                hInd)
              hRed₁ hBody
          with ⟨KΩ, hLiftLeft, hRedK₁⟩
        have hRedK₂ :
            Instance.reduct
                (productExecSchema_extension_right C₁ C₂
                  hInd)
                KΩ = I₂ := by
          calc
            _ = Instance.reduct
                (productExecSchema_extension_right
                  C₁ C₂ hInd) IΩ :=
              Cmd.onExtension_preserves_reduct
                (productExecSchema_extension_left C₁ C₂
                  hInd)
                (productExecSchema_extension_right C₁ C₂
                  hInd)
                (left_body_disjoint_right C₁ C₂ hInd)
                hLiftLeft
            _ = I₂ := hRed₂
        have hInv₁K := C₁.body_invariant hInv₁ hBody
        have hRightFalse :
            Cmd.BigStep (.while C₂.guard C₂.body) I₂
              I₂ :=
          Cmd.BigStep.while_false hG₂
        rcases ihLoop rfl (IΩ := KΩ)
            (I₂ := I₂) (J₂ := I₂) hRedK₁ hRedK₂
            hInv₁K hInv₂ hRightFalse
          with ⟨JΩ, hRest, hFinal₁, hFinal₂⟩
        have hStutter₂ := C₂.body_stutter hInv₂ hG₂
        have hLiftRight :
            Cmd.BigStep (rightBody C₁ C₂ hInd) KΩ KΩ
              :=
          Cmd.onExtension_bigStep_stutter
            (productExecSchema_extension_right C₁ C₂
              hInd)
            hRedK₂ hStutter₂
        refine ⟨JΩ, ?_, hFinal₁, hFinal₂⟩
        apply Cmd.BigStep.while_true
        · exact Or.inl
            ((leftGuard_eval_iff C₁ C₂ hInd IΩ).mpr
              (by simpa [hRed₁] using hG))
        · exact Cmd.BigStep.seq hLiftLeft hLiftRight
        · exact hRest
      · rcases hRightStep with
          ⟨L, hG₂, hBody₂, hLoop₂⟩
        rcases
            Cmd.onExtension_bigStep_lift
              (productExecSchema_extension_left C₁ C₂
                hInd)
              hRed₁ hBody
          with ⟨KΩ, hLiftLeft, hRedK₁⟩
        have hRedK₂ :
            Instance.reduct
                (productExecSchema_extension_right C₁ C₂
                  hInd)
                KΩ = I₂ := by
          calc
            _ = Instance.reduct
                (productExecSchema_extension_right
                  C₁ C₂ hInd) IΩ :=
              Cmd.onExtension_preserves_reduct
                (productExecSchema_extension_left C₁ C₂
                  hInd)
                (productExecSchema_extension_right C₁ C₂
                  hInd)
                (left_body_disjoint_right C₁ C₂ hInd)
                hLiftLeft
            _ = I₂ := hRed₂
        rcases
            Cmd.onExtension_bigStep_lift
              (productExecSchema_extension_right C₁ C₂
                hInd)
              hRedK₂ hBody₂
          with ⟨LΩ, hLiftRight, hRedL₂⟩
        have hRedL₁ :
            Instance.reduct
                (productExecSchema_extension_left C₁ C₂
                  hInd)
                LΩ = K := by
          calc
            _ = Instance.reduct
                (productExecSchema_extension_left
                  C₁ C₂ hInd) KΩ :=
              Cmd.onExtension_preserves_reduct
                (productExecSchema_extension_right C₁ C₂
                  hInd)
                (productExecSchema_extension_left C₁ C₂
                  hInd)
                (right_body_disjoint_left C₁ C₂ hInd)
                hLiftRight
            _ = K := hRedK₁
        have hInv₁K := C₁.body_invariant hInv₁ hBody
        have hInv₂L := C₂.body_invariant hInv₂
          hBody₂
        rcases ihLoop rfl (IΩ := LΩ)
            (I₂ := L) (J₂ := J₂) hRedL₁ hRedL₂
            hInv₁K hInv₂L hLoop₂
          with ⟨JΩ, hRest, hFinal₁, hFinal₂⟩
        refine ⟨JΩ, ?_, hFinal₁, hFinal₂⟩
        apply Cmd.BigStep.while_true
        · exact Or.inl
            ((leftGuard_eval_iff C₁ C₂ hInd IΩ).mpr
              (by simpa [hRed₁] using hG))
        · exact Cmd.BigStep.seq hLiftLeft hLiftRight
        · exact hRest

/- Two source loop runs combine into one lockstep run. -/
theorem productLoop_complete
    {I : Instance D (productExecSchema C₁ C₂ hInd)}
    {J₁ : Instance D C₁.program.execSchema}
    {J₂ : Instance D C₂.program.execSchema}
    (hInv₁ :
      C₁.invariant
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            I))
    (hInv₂ :
      C₂.invariant
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            I))
    (hLeft :
      Cmd.BigStep (.while C₁.guard C₁.body)
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            I)
        J₁)
    (hRight :
      Cmd.BigStep (.while C₂.guard C₂.body)
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            I)
        J₂) :
    ∃ J : Instance D (productExecSchema C₁ C₂ hInd),
      Cmd.BigStep
        (.while (productGuard C₁ C₂ hInd)
          (productBody C₁ C₂ hInd)) I J ∧
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            J =
        J₁ ∧
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            J =
        J₂ := by
  exact productLoop_complete_aux C₁ C₂ hInd hLeft rfl
    rfl rfl hInv₁ hInv₂ hRight

end ConcurrentProduct

end Whiel

------------------------------------------------------------
-- Whole Program Soundness
------------------------------------------------------------

namespace Whiel

namespace ConcurrentProduct

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable
  (C₁ C₂ : Component (A := A) (D := D))
  (hInd : Independent C₁ C₂)

private theorem left_init_disjoint_right
    (hInd : Independent C₁ C₂) :
    C₁.init.assignedSymbols ∩
        C₂.program.execSchema.syms = ∅ := by
  apply Finset.Subset.antisymm
  · intro X hX
    have hPair := Finset.mem_inter.mp hX
    have hBad : X ∈ C₁.writes ∩
        C₂.program.execSchema.syms :=
      Finset.mem_inter.mpr
        ⟨C₁.init_assigned_subset_writes hPair.1,
          hPair.2⟩
    rw [Independent.leftWritesExec hInd] at hBad
    exact hBad
  · exact Finset.empty_subset _

private theorem right_init_disjoint_left
    (hInd : Independent C₁ C₂) :
    C₂.init.assignedSymbols ∩
        C₁.program.execSchema.syms = ∅ := by
  apply Finset.Subset.antisymm
  · intro X hX
    have hPair := Finset.mem_inter.mp hX
    have hBad : X ∈ C₂.writes ∩
        C₁.program.execSchema.syms :=
      Finset.mem_inter.mpr
        ⟨C₂.init_assigned_subset_writes hPair.1,
          hPair.2⟩
    rw [Independent.rightWritesExec hInd] at hBad
    exact hBad
  · exact Finset.empty_subset _

private theorem left_close_disjoint_right
    (hInd : Independent C₁ C₂) :
    C₁.close.assignedSymbols ∩
        C₂.program.execSchema.syms = ∅ := by
  apply Finset.Subset.antisymm
  · intro X hX
    have hPair := Finset.mem_inter.mp hX
    have hBad : X ∈ C₁.writes ∩
        C₂.program.execSchema.syms :=
      Finset.mem_inter.mpr
        ⟨C₁.close_assigned_subset_writes hPair.1,
          hPair.2⟩
    rw [Independent.leftWritesExec hInd] at hBad
    exact hBad
  · exact Finset.empty_subset _

private theorem right_close_disjoint_left
    (hInd : Independent C₁ C₂) :
    C₂.close.assignedSymbols ∩
        C₁.program.execSchema.syms = ∅ := by
  apply Finset.Subset.antisymm
  · intro X hX
    have hPair := Finset.mem_inter.mp hX
    have hBad : X ∈ C₂.writes ∩
        C₁.program.execSchema.syms :=
      Finset.mem_inter.mpr
        ⟨C₂.close_assigned_subset_writes hPair.1,
          hPair.2⟩
    rw [Independent.rightWritesExec hInd] at hBad
    exact hBad
  · exact Finset.empty_subset _

/- Every product run projects to both source runs. -/
theorem product_bigStep_sound
    {I : Instance D (productInputSchema C₁ C₂ hInd)}
    {K : Instance D (productOutputSchema C₁ C₂ hInd)}
    (hProduct :
      (productProgram C₁ C₂ hInd).BigStep I K) :
    C₁.program.BigStep
        (Instance.reduct
          (productInputSchema_extension_left C₁ C₂ hInd)
            I)
        (Instance.reduct
          (productOutputSchema_extension_left C₁ C₂
            hInd) K) ∧
      C₂.program.BigStep
        (Instance.reduct
          (productInputSchema_extension_right C₁ C₂
            hInd) I)
        (Instance.reduct
          (productOutputSchema_extension_right C₁ C₂
            hInd)
          K) := by
  rcases hProduct with ⟨J, hCommand, hObserve⟩
  change Cmd.BigStep (productCommand C₁ C₂ hInd)
      ((productProgram C₁ C₂ hInd).initialInstance I) J
    at hCommand
  unfold productCommand Cmd.framedLoopCommand at hCommand
  rw [Cmd.bigStep_seq_iff] at hCommand
  rcases hCommand with ⟨T, hInitLoop, hClose⟩
  rw [Cmd.bigStep_seq_iff] at hInitLoop
  rcases hInitLoop with ⟨S, hInit, hLoop⟩
  unfold productInit at hInit
  rw [Cmd.bigStep_seq_iff] at hInit
  rcases hInit with ⟨M, hInit₁, hInit₂⟩
  unfold productClose at hClose
  rw [Cmd.bigStep_seq_iff] at hClose
  rcases hClose with ⟨U, hClose₁, hClose₂⟩
  have hInitStep₁ :=
    Cmd.onExtension_bigStep_reduct
      (productExecSchema_extension_left C₁ C₂ hInd)
      hInit₁
  have hInitStep₂ :=
    Cmd.onExtension_bigStep_reduct
      (productExecSchema_extension_right C₁ C₂ hInd)
      hInit₂
  have hInitLeftFrame :
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            S =
        Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            M :=
    Cmd.onExtension_preserves_reduct
      (productExecSchema_extension_right C₁ C₂ hInd)
      (productExecSchema_extension_left C₁ C₂ hInd)
      (right_init_disjoint_left C₁ C₂ hInd) hInit₂
  have hInitRightFrame :
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            M =
        Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          ((productProgram C₁ C₂ hInd).initialInstance
            I) :=
    Cmd.onExtension_preserves_reduct
      (productExecSchema_extension_left C₁ C₂ hInd)
      (productExecSchema_extension_right C₁ C₂ hInd)
      (left_init_disjoint_right C₁ C₂ hInd) hInit₁
  have hSourceInit₁ :
      Cmd.BigStep C₁.init
        (C₁.program.initialInstance
          (Instance.reduct
            (productInputSchema_extension_left C₁ C₂
              hInd)
            I))
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            S) := by
    rw [hInitLeftFrame]
    rw [← reduct_product_initial_left C₁ C₂ hInd I]
    exact hInitStep₁
  have hSourceInit₂ :
      Cmd.BigStep C₂.init
        (C₂.program.initialInstance
          (Instance.reduct
            (productInputSchema_extension_right C₁ C₂
              hInd)
            I))
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            S) := by
    rw [← reduct_product_initial_right C₁ C₂ hInd I]
    rw [← hInitRightFrame]
    exact hInitStep₂
  have hInv₁ := C₁.init_invariant _ hSourceInit₁
  have hInv₂ := C₂.init_invariant _ hSourceInit₂
  have hLoops :=
    productLoop_sound C₁ C₂ hInd hInv₁ hInv₂ hLoop
  have hCloseStep₁ :=
    Cmd.onExtension_bigStep_reduct
      (productExecSchema_extension_left C₁ C₂ hInd)
      hClose₁
  have hCloseStep₂ :=
    Cmd.onExtension_bigStep_reduct
      (productExecSchema_extension_right C₁ C₂ hInd)
      hClose₂
  have hCloseLeftFrame :
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            J =
        Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            U :=
    Cmd.onExtension_preserves_reduct
      (productExecSchema_extension_right C₁ C₂ hInd)
      (productExecSchema_extension_left C₁ C₂ hInd)
      (right_close_disjoint_left C₁ C₂ hInd) hClose₂
  have hCloseRightFrame :
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            U =
        Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            T :=
    Cmd.onExtension_preserves_reduct
      (productExecSchema_extension_left C₁ C₂ hInd)
      (productExecSchema_extension_right C₁ C₂ hInd)
      (left_close_disjoint_right C₁ C₂ hInd) hClose₁
  have hSourceClose₁ :
      Cmd.BigStep C₁.close
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            T)
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            J) := by
    rw [hCloseLeftFrame]
    exact hCloseStep₁
  have hSourceClose₂ :
      Cmd.BigStep C₂.close
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            T)
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            J) := by
    rw [← hCloseRightFrame]
    exact hCloseStep₂
  constructor
  · refine ⟨Instance.reduct
        (productExecSchema_extension_left C₁ C₂ hInd) J,
      ?_, ?_⟩
    · apply (C₁.cmd_equiv _ _).mpr
      exact Cmd.BigStep.seq
        (Cmd.BigStep.seq hSourceInit₁ hLoops.1)
        hSourceClose₁
    · calc
        C₁.program.observe
            (Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd) J) =
            Instance.reduct
              (productOutputSchema_extension_left C₁ C₂
                hInd)
              ((productProgram C₁ C₂ hInd).observe J) :=
          (reduct_product_observe_left C₁ C₂ hInd
            J).symm
        _ = Instance.reduct
              (productOutputSchema_extension_left C₁ C₂
                hInd) K :=
          congrArg
            (Instance.reduct
              (productOutputSchema_extension_left C₁ C₂
                hInd))
            hObserve
  · refine ⟨Instance.reduct
        (productExecSchema_extension_right C₁ C₂ hInd)
          J,
      ?_, ?_⟩
    · apply (C₂.cmd_equiv _ _).mpr
      exact Cmd.BigStep.seq
        (Cmd.BigStep.seq hSourceInit₂ hLoops.2)
        hSourceClose₂
    · calc
        C₂.program.observe
            (Instance.reduct
              (productExecSchema_extension_right C₁ C₂
                hInd) J) =
            Instance.reduct
              (productOutputSchema_extension_right C₁ C₂
                hInd)
              ((productProgram C₁ C₂ hInd).observe J) :=
          (reduct_product_observe_right C₁ C₂ hInd
            J).symm
        _ = Instance.reduct
              (productOutputSchema_extension_right C₁ C₂
                hInd)
              K :=
          congrArg
            (Instance.reduct
              (productOutputSchema_extension_right C₁ C₂
                hInd))
            hObserve

/- The two output projections determine a product output. -/
private theorem productOutput_ext
    {K L : Instance D (productOutputSchema C₁ C₂ hInd)}
    (hLeft :
      Instance.reduct
          (productOutputSchema_extension_left C₁ C₂
            hInd) K =
        Instance.reduct
          (productOutputSchema_extension_left C₁ C₂
            hInd) L)
    (hRight :
      Instance.reduct
          (productOutputSchema_extension_right C₁ C₂
            hInd) K =
        Instance.reduct
          (productOutputSchema_extension_right C₁ C₂
            hInd) L) :
    K = L := by
  apply Instance.ext
  intro X
  have hMem :
      X.1 ∈ C₁.outputSchema.syms ∪
        C₂.outputSchema.syms := by
    exact X.2
  rcases Finset.mem_union.mp hMem with hX | hX
  · have hAt := congrFun hLeft ⟨X.1, hX⟩
    unfold Instance.reduct at hAt
    simpa using hAt
  · have hAt := congrFun hRight ⟨X.1, hX⟩
    unfold Instance.reduct at hAt
    simpa using hAt

/- Two source runs lift to a product run. -/
theorem product_bigStep_complete
    {I : Instance D (productInputSchema C₁ C₂ hInd)}
    {K : Instance D (productOutputSchema C₁ C₂ hInd)}
    (hLeft :
      C₁.program.BigStep
        (Instance.reduct
          (productInputSchema_extension_left C₁ C₂ hInd)
            I)
        (Instance.reduct
          (productOutputSchema_extension_left C₁ C₂
            hInd) K))
    (hRight :
      C₂.program.BigStep
        (Instance.reduct
          (productInputSchema_extension_right C₁ C₂
            hInd) I)
        (Instance.reduct
          (productOutputSchema_extension_right C₁ C₂
            hInd)
          K)) :
    (productProgram C₁ C₂ hInd).BigStep I K := by
  rcases hLeft with ⟨J₁, hCommand₁, hObserve₁⟩
  rcases hRight with ⟨J₂, hCommand₂, hObserve₂⟩
  have hFramed₁ := (C₁.cmd_equiv _ _).mp hCommand₁
  have hFramed₂ := (C₂.cmd_equiv _ _).mp hCommand₂
  unfold Cmd.framedLoopCommand at hFramed₁ hFramed₂
  rw [Cmd.bigStep_seq_iff] at hFramed₁ hFramed₂
  rcases hFramed₁ with ⟨T₁, hInitLoop₁, hClose₁⟩
  rcases hFramed₂ with ⟨T₂, hInitLoop₂, hClose₂⟩
  rw [Cmd.bigStep_seq_iff] at hInitLoop₁ hInitLoop₂
  rcases hInitLoop₁ with ⟨S₁, hInit₁, hLoop₁⟩
  rcases hInitLoop₂ with ⟨S₂, hInit₂, hLoop₂⟩
  let IΩ := (productProgram C₁ C₂ hInd).initialInstance
    I
  have hInitial₁ :
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            IΩ =
        C₁.program.initialInstance
          (Instance.reduct
            (productInputSchema_extension_left C₁ C₂
              hInd)
            I) := by
    exact reduct_product_initial_left C₁ C₂ hInd I
  rcases
      Cmd.onExtension_bigStep_lift
        (productExecSchema_extension_left C₁ C₂ hInd)
        hInitial₁ hInit₁
    with ⟨M, hLiftInit₁, hRedM₁⟩
  have hRedM₂ :
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            M =
        C₂.program.initialInstance
          (Instance.reduct
            (productInputSchema_extension_right C₁ C₂
              hInd)
            I) := by
    calc
      _ = Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            IΩ :=
        Cmd.onExtension_preserves_reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          (productExecSchema_extension_right C₁ C₂ hInd)
          (left_init_disjoint_right C₁ C₂ hInd)
          hLiftInit₁
      _ = _ := reduct_product_initial_right C₁ C₂ hInd I
  rcases
      Cmd.onExtension_bigStep_lift
        (productExecSchema_extension_right C₁ C₂ hInd)
        hRedM₂ hInit₂
    with ⟨S, hLiftInit₂, hRedS₂⟩
  have hRedS₁ :
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            S =
        S₁ := by
    calc
      _ = Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            M :=
        Cmd.onExtension_preserves_reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          (productExecSchema_extension_left C₁ C₂ hInd)
          (right_init_disjoint_left C₁ C₂ hInd)
          hLiftInit₂
      _ = S₁ := hRedM₁
  have hInv₁ :
      C₁.invariant
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            S) := by
    rw [hRedS₁]
    exact C₁.init_invariant _ hInit₁
  have hInv₂ :
      C₂.invariant
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            S) := by
    rw [hRedS₂]
    exact C₂.init_invariant _ hInit₂
  have hLoop₁' :
      Cmd.BigStep (.while C₁.guard C₁.body)
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            S)
        T₁ := by
    rw [hRedS₁]
    exact hLoop₁
  have hLoop₂' :
      Cmd.BigStep (.while C₂.guard C₂.body)
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            S)
        T₂ := by
    rw [hRedS₂]
    exact hLoop₂
  rcases
      productLoop_complete C₁ C₂ hInd hInv₁ hInv₂
        hLoop₁' hLoop₂'
    with ⟨T, hLiftLoop, hRedT₁, hRedT₂⟩
  rcases
      Cmd.onExtension_bigStep_lift
        (productExecSchema_extension_left C₁ C₂ hInd)
        hRedT₁ hClose₁
    with ⟨U, hLiftClose₁, hRedU₁⟩
  have hRedU₂ :
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            U =
        T₂ := by
    calc
      _ = Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            T :=
        Cmd.onExtension_preserves_reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
          (productExecSchema_extension_right C₁ C₂ hInd)
          (left_close_disjoint_right C₁ C₂ hInd)
          hLiftClose₁
      _ = T₂ := hRedT₂
  rcases
      Cmd.onExtension_bigStep_lift
        (productExecSchema_extension_right C₁ C₂ hInd)
        hRedU₂ hClose₂
    with ⟨J, hLiftClose₂, hRedJ₂⟩
  have hRedJ₁ :
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            J =
        J₁ := by
    calc
      _ = Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            U :=
        Cmd.onExtension_preserves_reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          (productExecSchema_extension_left C₁ C₂ hInd)
          (right_close_disjoint_left C₁ C₂ hInd)
          hLiftClose₂
      _ = J₁ := hRedU₁
  have hOutput :
      (productProgram C₁ C₂ hInd).observe J = K := by
    apply productOutput_ext C₁ C₂ hInd
    · calc
        Instance.reduct
            (productOutputSchema_extension_left C₁ C₂
              hInd)
            ((productProgram C₁ C₂ hInd).observe J) =
          C₁.program.observe
            (Instance.reduct
              (productExecSchema_extension_left C₁ C₂
                hInd) J) :=
          reduct_product_observe_left C₁ C₂ hInd J
        _ = C₁.program.observe J₁ :=
          congrArg C₁.program.observe hRedJ₁
        _ = Instance.reduct
              (productOutputSchema_extension_left C₁ C₂
                hInd) K :=
          hObserve₁
    · calc
        Instance.reduct
            (productOutputSchema_extension_right C₁ C₂
              hInd)
            ((productProgram C₁ C₂ hInd).observe J) =
          C₂.program.observe
            (Instance.reduct
              (productExecSchema_extension_right C₁ C₂
                hInd) J) :=
          reduct_product_observe_right C₁ C₂ hInd J
        _ = C₂.program.observe J₂ :=
          congrArg C₂.program.observe hRedJ₂
        _ = Instance.reduct
              (productOutputSchema_extension_right C₁ C₂
                hInd) K :=
          hObserve₂
  refine ⟨J, ?_, hOutput⟩
  change Cmd.BigStep (productCommand C₁ C₂ hInd) IΩ J
  unfold productCommand Cmd.framedLoopCommand
  exact Cmd.BigStep.seq
    (Cmd.BigStep.seq
      (Cmd.BigStep.seq hLiftInit₁ hLiftInit₂)
      hLiftLoop)
    (Cmd.BigStep.seq hLiftClose₁ hLiftClose₂)

/- Product execution is exactly paired source execution. -/
theorem product_bigStep_iff
    {I : Instance D (productInputSchema C₁ C₂ hInd)}
    {K : Instance D (productOutputSchema C₁ C₂ hInd)} :
    (productProgram C₁ C₂ hInd).BigStep I K ↔
      C₁.program.BigStep
          (Instance.reduct
            (productInputSchema_extension_left C₁ C₂
              hInd) I)
          (Instance.reduct
            (productOutputSchema_extension_left C₁ C₂
              hInd) K) ∧
        C₂.program.BigStep
          (Instance.reduct
            (productInputSchema_extension_right C₁ C₂
              hInd) I)
          (Instance.reduct
            (productOutputSchema_extension_right C₁ C₂
              hInd)
            K) := by
  constructor
  · exact product_bigStep_sound C₁ C₂ hInd
  · rintro ⟨hLeft, hRight⟩
    exact product_bigStep_complete C₁ C₂ hInd hLeft
      hRight

end ConcurrentProduct

end Whiel

------------------------------------------------------------
-- Product Component Certificate
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/- Retagging preserves all command symbols. -/
@[simp] theorem symbols_onExtension
    (hExt : Ω.extensionOf Γ)
    (C : Cmd D Γ) :
    (C.onExtension hExt).symbols = C.symbols := by
  induction C with
  | skip =>
      simp [onExtension, symbols]
  | assign X e =>
      simp [onExtension, symbols,
        UnnamedSchema.symOfExtension, RAExpr.symbols,
        RAExpr.castArity, RAExpr.onExtension]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [onExtension, symbols, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [onExtension, symbols, ih₁, ih₂]
  | «while» G C ih =>
      simp [onExtension, symbols, ih]

end Cmd

namespace ConcurrentProduct

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable
  (C₁ C₂ : Component (A := A) (D := D))
  (hInd : Independent C₁ C₂)

/- Local invariants paired over the product state. -/
def productInvariant
    (I : Instance D (productExecSchema C₁ C₂ hInd)) :
    Prop :=
  C₁.invariant
      (Instance.reduct
        (productExecSchema_extension_left C₁ C₂ hInd) I)
          ∧
    C₂.invariant
      (Instance.reduct
        (productExecSchema_extension_right C₁ C₂ hInd)
          I)

private theorem agreeOn_left_reduct
    {I J : Instance D (productExecSchema C₁ C₂ hInd)}
    (hAgree :
      Instance.agreeOn (C₁.footprint ∪ C₂.footprint) I
        J) :
    Instance.agreeOn C₁.footprint
      (Instance.reduct
        (productExecSchema_extension_left C₁ C₂ hInd) I)
      (Instance.reduct
        (productExecSchema_extension_left C₁ C₂ hInd) J)
          := by
  intro X hX
  have hGlobal := hAgree
    (UnnamedSchema.symOfExtension
      (productExecSchema_extension_left C₁ C₂ hInd) X)
    (Finset.mem_union_left _ hX)
  unfold Instance.reduct
  simpa using hGlobal

private theorem agreeOn_right_reduct
    {I J : Instance D (productExecSchema C₁ C₂ hInd)}
    (hAgree :
      Instance.agreeOn (C₁.footprint ∪ C₂.footprint) I
        J) :
    Instance.agreeOn C₂.footprint
      (Instance.reduct
        (productExecSchema_extension_right C₁ C₂ hInd)
          I)
      (Instance.reduct
        (productExecSchema_extension_right C₁ C₂ hInd)
          J) := by
  intro X hX
  have hGlobal := hAgree
    (UnnamedSchema.symOfExtension
      (productExecSchema_extension_right C₁ C₂ hInd) X)
    (Finset.mem_union_right _ hX)
  unfold Instance.reduct
  simpa using hGlobal

private theorem product_init_invariant
    (I : Instance D (productInputSchema C₁ C₂ hInd))
    {J : Instance D (productExecSchema C₁ C₂ hInd)}
    (hStep :
      Cmd.BigStep (productInit C₁ C₂ hInd)
        ((productProgram C₁ C₂ hInd).initialInstance I)
          J) :
    productInvariant C₁ C₂ hInd J := by
  unfold productInit at hStep
  rw [Cmd.bigStep_seq_iff] at hStep
  rcases hStep with ⟨M, hInit₁, hInit₂⟩
  have hLocal₁ :=
    Cmd.onExtension_bigStep_reduct
      (productExecSchema_extension_left C₁ C₂ hInd)
        hInit₁
  have hLocal₂ :=
    Cmd.onExtension_bigStep_reduct
      (productExecSchema_extension_right C₁ C₂ hInd)
        hInit₂
  have hFrame₁ :
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            J =
        Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            M :=
    Cmd.onExtension_preserves_reduct
      (productExecSchema_extension_right C₁ C₂ hInd)
      (productExecSchema_extension_left C₁ C₂ hInd)
      (right_init_disjoint_left C₁ C₂ hInd) hInit₂
  have hFrame₂ :
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            M =
        Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
          ((productProgram C₁ C₂ hInd).initialInstance
            I) :=
    Cmd.onExtension_preserves_reduct
      (productExecSchema_extension_left C₁ C₂ hInd)
      (productExecSchema_extension_right C₁ C₂ hInd)
      (left_init_disjoint_right C₁ C₂ hInd) hInit₁
  constructor
  · rw [hFrame₁]
    apply C₁.init_invariant
      (Instance.reduct
        (productInputSchema_extension_left C₁ C₂ hInd)
          I)
    rw [← reduct_product_initial_left C₁ C₂ hInd I]
    exact hLocal₁
  · apply C₂.init_invariant
      (Instance.reduct
        (productInputSchema_extension_right C₁ C₂ hInd)
          I)
    rw [← reduct_product_initial_right C₁ C₂ hInd I]
    rw [← hFrame₂]
    exact hLocal₂

private theorem product_body_invariant
    {I J : Instance D (productExecSchema C₁ C₂ hInd)}
    (hInv : productInvariant C₁ C₂ hInd I)
    (hStep : Cmd.BigStep (productBody C₁ C₂ hInd) I J) :
    productInvariant C₁ C₂ hInd J := by
  unfold productBody at hStep
  rw [Cmd.bigStep_seq_iff] at hStep
  rcases hStep with ⟨M, hBody₁, hBody₂⟩
  have hLocal₁ :=
    Cmd.onExtension_bigStep_reduct
      (productExecSchema_extension_left C₁ C₂ hInd)
        hBody₁
  have hLocal₂ :=
    Cmd.onExtension_bigStep_reduct
      (productExecSchema_extension_right C₁ C₂ hInd)
        hBody₂
  have hFrame₁ :
      Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            J =
        Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            M :=
    Cmd.onExtension_preserves_reduct
      (productExecSchema_extension_right C₁ C₂ hInd)
      (productExecSchema_extension_left C₁ C₂ hInd)
      (right_body_disjoint_left C₁ C₂ hInd) hBody₂
  have hFrame₂ :
      Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            M =
        Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            I :=
    Cmd.onExtension_preserves_reduct
      (productExecSchema_extension_left C₁ C₂ hInd)
      (productExecSchema_extension_right C₁ C₂ hInd)
      (left_body_disjoint_right C₁ C₂ hInd) hBody₁
  constructor
  · rw [hFrame₁]
    exact C₁.body_invariant hInv.1 hLocal₁
  · have hInvM :
        C₂.invariant
          (Instance.reduct
            (productExecSchema_extension_right C₁ C₂
              hInd)
            M) := by
      rw [hFrame₂]
      exact hInv.2
    exact C₂.body_invariant hInvM hLocal₂

private theorem product_body_stutter
    {I : Instance D (productExecSchema C₁ C₂ hInd)}
    (hInv : productInvariant C₁ C₂ hInd I)
    (hDone : ¬ (productGuard C₁ C₂ hInd).eval I) :
    Cmd.BigStep (productBody C₁ C₂ hInd) I I := by
  have hDoneLeft :
      ¬ C₁.guard.eval
        (Instance.reduct
          (productExecSchema_extension_left C₁ C₂ hInd)
            I) := by
    intro hEval
    apply hDone
    exact Or.inl
      ((leftGuard_eval_iff C₁ C₂ hInd I).mpr hEval)
  have hDoneRight :
      ¬ C₂.guard.eval
        (Instance.reduct
          (productExecSchema_extension_right C₁ C₂ hInd)
            I) := by
    intro hEval
    apply hDone
    exact Or.inr
      ((rightGuard_eval_iff C₁ C₂ hInd I).mpr hEval)
  have hLocal₁ := C₁.body_stutter hInv.1 hDoneLeft
  have hLocal₂ := C₂.body_stutter hInv.2 hDoneRight
  have hLift₁ :
      Cmd.BigStep (leftBody C₁ C₂ hInd) I I :=
    Cmd.onExtension_bigStep_stutter
      (productExecSchema_extension_left C₁ C₂ hInd)
      rfl hLocal₁
  have hLift₂ :
      Cmd.BigStep (rightBody C₁ C₂ hInd) I I :=
    Cmd.onExtension_bigStep_stutter
      (productExecSchema_extension_right C₁ C₂ hInd)
      rfl hLocal₂
  exact Cmd.BigStep.seq hLift₁ hLift₂

/- The concurrent product is itself a certified component.
  -/
def product : Component (A := A) (D := D) where
  inputSchema := productInputSchema C₁ C₂ hInd
  outputSchema := productOutputSchema C₁ C₂ hInd
  program := productProgram C₁ C₂ hInd
  init := productInit C₁ C₂ hInd
  guard := productGuard C₁ C₂ hInd
  body := productBody C₁ C₂ hInd
  close := productClose C₁ C₂ hInd
  footprint := C₁.footprint ∪ C₂.footprint
  footprint_subset := by
    intro X hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact
        (productExecSchema_extension_left C₁ C₂ hInd).1
          (C₁.footprint_subset hX)
    · exact
        (productExecSchema_extension_right C₁ C₂ hInd).1
          (C₂.footprint_subset hX)
  input_subset := by
    intro X hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact Finset.mem_union_left _ (C₁.input_subset hX)
    · exact Finset.mem_union_right _ (C₂.input_subset hX)
  output_subset := by
    intro X hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact Finset.mem_union_left _ (C₁.output_subset hX)
    · exact Finset.mem_union_right _ (C₂.output_subset
      hX)
  init_symbols := by
    intro X hX
    rcases Finset.mem_union.mp hX with hX | hX
    · apply Finset.mem_union_left
      apply C₁.init_symbols
      unfold leftInit at hX
      exact (congrArg (fun S : Finset A => X ∈ S)
        (Cmd.symbols_onExtension
          (productExecSchema_extension_left C₁ C₂ hInd)
          C₁.init)).mp hX
    · apply Finset.mem_union_right
      apply C₂.init_symbols
      unfold rightInit at hX
      exact (congrArg (fun S : Finset A => X ∈ S)
        (Cmd.symbols_onExtension
          (productExecSchema_extension_right C₁ C₂ hInd)
          C₂.init)).mp hX
  guard_symbols := by
    intro X hX
    rcases Finset.mem_union.mp hX with hX | hX
    · apply Finset.mem_union_left
      apply C₁.guard_symbols
      unfold leftGuard at hX
      exact (congrArg (fun S : Finset A => X ∈ S)
        (Guard.symbols_onExtension
          (productExecSchema_extension_left C₁ C₂ hInd)
          C₁.guard)).mp hX
    · apply Finset.mem_union_right
      apply C₂.guard_symbols
      unfold rightGuard at hX
      exact (congrArg (fun S : Finset A => X ∈ S)
        (Guard.symbols_onExtension
          (productExecSchema_extension_right C₁ C₂ hInd)
          C₂.guard)).mp hX
  body_symbols := by
    intro X hX
    rcases Finset.mem_union.mp hX with hX | hX
    · apply Finset.mem_union_left
      apply C₁.body_symbols
      unfold leftBody at hX
      exact (congrArg (fun S : Finset A => X ∈ S)
        (Cmd.symbols_onExtension
          (productExecSchema_extension_left C₁ C₂ hInd)
          C₁.body)).mp hX
    · apply Finset.mem_union_right
      apply C₂.body_symbols
      unfold rightBody at hX
      exact (congrArg (fun S : Finset A => X ∈ S)
        (Cmd.symbols_onExtension
          (productExecSchema_extension_right C₁ C₂ hInd)
          C₂.body)).mp hX
  close_symbols := by
    intro X hX
    rcases Finset.mem_union.mp hX with hX | hX
    · apply Finset.mem_union_left
      apply C₁.close_symbols
      unfold leftClose at hX
      exact (congrArg (fun S : Finset A => X ∈ S)
        (Cmd.symbols_onExtension
          (productExecSchema_extension_left C₁ C₂ hInd)
          C₁.close)).mp hX
    · apply Finset.mem_union_right
      apply C₂.close_symbols
      unfold rightClose at hX
      exact (congrArg (fun S : Finset A => X ∈ S)
        (Cmd.symbols_onExtension
          (productExecSchema_extension_right C₁ C₂ hInd)
          C₂.close)).mp hX
  init_loopFree :=
    Cmd.loopFree_seq
      ((Cmd.loopFree_onExtension
        (productExecSchema_extension_left C₁ C₂ hInd)
        C₁.init).mpr C₁.init_loopFree)
      ((Cmd.loopFree_onExtension
        (productExecSchema_extension_right C₁ C₂ hInd)
        C₂.init).mpr C₂.init_loopFree)
  body_loopFree :=
    Cmd.loopFree_seq
      ((Cmd.loopFree_onExtension
        (productExecSchema_extension_left C₁ C₂ hInd)
        C₁.body).mpr C₁.body_loopFree)
      ((Cmd.loopFree_onExtension
        (productExecSchema_extension_right C₁ C₂ hInd)
        C₂.body).mpr C₂.body_loopFree)
  close_loopFree :=
    Cmd.loopFree_seq
      ((Cmd.loopFree_onExtension
        (productExecSchema_extension_left C₁ C₂ hInd)
        C₁.close).mpr C₁.close_loopFree)
      ((Cmd.loopFree_onExtension
        (productExecSchema_extension_right C₁ C₂ hInd)
        C₂.close).mpr C₂.close_loopFree)
  invariant := productInvariant C₁ C₂ hInd
  invariant_local := by
    intro I J hAgree
    unfold productInvariant
    constructor
    · rintro ⟨hInv₁, hInv₂⟩
      exact
        ⟨(C₁.invariant_local
          (agreeOn_left_reduct C₁ C₂ hInd hAgree)).mp
            hInv₁,
        (C₂.invariant_local
          (agreeOn_right_reduct C₁ C₂ hInd hAgree)).mp
            hInv₂⟩
    · rintro ⟨hInv₁, hInv₂⟩
      exact
        ⟨(C₁.invariant_local
          (agreeOn_left_reduct C₁ C₂ hInd hAgree)).mpr
            hInv₁,
        (C₂.invariant_local
          (agreeOn_right_reduct C₁ C₂ hInd hAgree)).mpr
            hInv₂⟩
  init_invariant := product_init_invariant C₁ C₂ hInd
  body_invariant := product_body_invariant C₁ C₂ hInd
  body_stutter := product_body_stutter C₁ C₂ hInd
  cmd_equiv := by
    intro I J
    rfl

/- The product guard is the lifted disjunction. -/
theorem product_guard_eq :
    (product C₁ C₂ hInd).guard =
      .or (leftGuard C₁ C₂ hInd)
        (rightGuard C₁ C₂ hInd) := by
  rfl

/- Both lifted bodies run in left-to-right order. -/
theorem product_body_eq :
    (product C₁ C₂ hInd).body =
      .seq (leftBody C₁ C₂ hInd)
        (rightBody C₁ C₂ hInd) := by
  rfl

/- The product command contains exactly one while. -/
theorem productCommand_whileCount :
    (productCommand C₁ C₂ hInd).whileCount = 1 := by
  have hInit :
      (productInit C₁ C₂ hInd).whileCount = 0 :=
    Cmd.whileCount_eq_zero_of_loopFree
      (product C₁ C₂ hInd).init_loopFree
  have hBody :
      (productBody C₁ C₂ hInd).whileCount = 0 :=
    Cmd.whileCount_eq_zero_of_loopFree
      (product C₁ C₂ hInd).body_loopFree
  have hClose :
      (productClose C₁ C₂ hInd).whileCount = 0 :=
    Cmd.whileCount_eq_zero_of_loopFree
      (product C₁ C₂ hInd).close_loopFree
  simp [productCommand, Cmd.framedLoopCommand,
    Cmd.whileCount, hInit, hBody, hClose]

end ConcurrentProduct

end Whiel
