-- Author: Jesse Comer
import Whiel.Guard.Syntax

/-
  Core Whiel syntax and observable program interfaces.

  Key declarations: `Guard`, `Cmd`, and `Program`.
  A `Cmd` is typed by a full execution schema.  A
  `Program` exposes input and output schemas while retaining
  a full execution schema that may contain auxiliary
  relation symbols.
-/

------------------------------------------------------------
-- Commands
------------------------------------------------------------

namespace Whiel

/-
  Commands over a full execution schema `Γ`.

  Assignment is intrinsically well-typed: the left-hand side
  is a relation name of `Γ`, and the right-hand side is a
  relational algebra expression of the same arity.
-/
inductive Cmd
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type
| skip : Cmd D Γ
| assign
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    Cmd D Γ
| seq
    (C₁ C₂ : Cmd D Γ) :
    Cmd D Γ
| ite
    (G : Guard D Γ)
    (C₁ C₂ : Cmd D Γ) :
    Cmd D Γ
| «while»
    (G : Guard D Γ)
    (C : Cmd D Γ) :
    Cmd D Γ

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Relation names assigned by a command. -/
def assignedSymbols : Cmd D Γ → Finset A
| .skip => ∅
| .assign X _ => {X.1}
| .seq C₁ C₂ =>
    C₁.assignedSymbols ∪ C₂.assignedSymbols
| .ite _ C₁ C₂ =>
    C₁.assignedSymbols ∪ C₂.assignedSymbols
| .while _ C =>
    C.assignedSymbols

/- Relation names read or assigned by a command. -/
def symbols : Cmd D Γ → Finset A
| .skip => ∅
| .assign X e =>
    {X.1} ∪ e.symbols
| .seq C₁ C₂ =>
    C₁.symbols ∪ C₂.symbols
| .ite G C₁ C₂ =>
    G.symbols ∪ C₁.symbols ∪ C₂.symbols
| .while G C =>
    G.symbols ∪ C.symbols

/- Assigned symbols are always schema symbols. -/
theorem assignedSymbols_subset_syms
    (C : Cmd D Γ) :
    C.assignedSymbols ⊆ Γ.syms := by
  induction C with
  | skip =>
      intro X hX
      simp [Cmd.assignedSymbols] at hX
  | assign X e =>
      intro Y hY
      have hYX : Y = X.1 := by
        simpa [Cmd.assignedSymbols] using hY
      simp [hYX, X.2]
  | seq C₁ C₂ ih₁ ih₂ =>
      intro X hX
      have hCases :
          X ∈ C₁.assignedSymbols ∨
            X ∈ C₂.assignedSymbols := by
        simpa [Cmd.assignedSymbols] using hX
      cases hCases with
      | inl hMem => exact ih₁ hMem
      | inr hMem => exact ih₂ hMem
  | ite G C₁ C₂ ih₁ ih₂ =>
      intro X hX
      have hCases :
          X ∈ C₁.assignedSymbols ∨
            X ∈ C₂.assignedSymbols := by
        simpa [Cmd.assignedSymbols] using hX
      cases hCases with
      | inl hMem => exact ih₁ hMem
      | inr hMem => exact ih₂ hMem
  | «while» G C ih =>
      intro X hX
      exact ih hX

/- Assigned symbols are among all command symbols. -/
theorem assignedSymbols_subset_symbols
    (C : Cmd D Γ) :
    C.assignedSymbols ⊆ C.symbols := by
  induction C with
  | skip =>
      simp [assignedSymbols, symbols]
  | assign X e =>
      simp [assignedSymbols, symbols]
  | seq C₁ C₂ ih₁ ih₂ =>
      simpa [assignedSymbols, symbols] using
        Finset.union_subset_union ih₁ ih₂
  | ite G C₁ C₂ ih₁ ih₂ =>
      intro X hX
      simp only [assignedSymbols, Finset.mem_union] at hX
      simp only [symbols, Finset.mem_union]
      rcases hX with hX | hX
      · exact Or.inl (Or.inr (ih₁ hX))
      · exact Or.inr (ih₂ hX)
  | «while» G C ih =>
      intro X hX
      simp only [assignedSymbols] at hX
      simp only [symbols, Finset.mem_union]
      exact Or.inr (ih hX)

/- Domain constants occurring in a command. -/
def constants : Cmd D Γ → Finset D
| .skip => ∅
| .assign _ e =>
    e.constants
| .seq C₁ C₂ =>
    C₁.constants ∪ C₂.constants
| .ite G C₁ C₂ =>
    G.constants ∪ C₁.constants ∪ C₂.constants
| .while G C =>
    G.constants ∪ C.constants

/- Derived constructor for assignments from a raw name. -/
def assignRel
    (X : A)
    (hX : X ∈ Γ.syms)
    (e : RAExpr D Γ (Γ.arity ⟨X, hX⟩)) :
    Cmd D Γ :=
  .assign ⟨X, hX⟩ e

end Cmd

end Whiel

------------------------------------------------------------
-- Programs
------------------------------------------------------------

namespace Whiel

/-
  A Whiel program with input schema `Δ` and output schema
  `Λ`.

  The command itself runs over `execSchema`, which may
  include auxiliary relation symbols that are not observable
  in the final result.
-/
structure Program
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Δ Λ : UnnamedSchema A) where
  execSchema : UnnamedSchema A
  extendsInput : execSchema.extensionOf Δ
  extendsOutput : execSchema.extensionOf Λ
  cmd : Cmd D execSchema

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Λ : UnnamedSchema A}

/- Execution symbols not visible in the external output. -/
def hiddenSymbols
    (P : Program D Δ Λ) : Finset A :=
  P.execSchema.syms \ Λ.syms

/- Assigned symbols of the underlying command. -/
def assignedSymbols
    (P : Program D Δ Λ) : Finset A :=
  P.cmd.assignedSymbols

/-
  Treat a command as a program whose input, output, and
  execution schemas coincide.
-/
def ofCmd
    {Γ : UnnamedSchema A}
    (C : Cmd D Γ) :
    Program D Γ Γ where
  execSchema := Γ
  extendsInput := UnnamedSchema.extensionOf_refl Γ
  extendsOutput := UnnamedSchema.extensionOf_refl Γ
  cmd := C

end Program

end Whiel

------------------------------------------------------------
-- Raw Command Syntax And Checking
------------------------------------------------------------

/-
  Raw Whiel command syntax.

  This layer is syntactic infrastructure for notation and
  compiler construction. It has no separate semantics:
  well-formed raw commands are checked into typed `Cmd`s
  before execution.
-/

namespace Whiel

/-
  Raw commands over relation names `A`.

  Assignment stores a raw left-hand relation name and a raw
  RA expression. Schema membership and arity agreement are
  checked by `RawCmd.toCmd?`.
-/
inductive RawCmd
    (A D : Type)
    [RelationNames A]
    [Domain D] : Type
| skip : RawCmd A D
| assign (X : A) (e : RawRAExpr A D) : RawCmd A D
| assignEmpty (X : A) : RawCmd A D
| seq (C₁ C₂ : RawCmd A D) : RawCmd A D
| ite (G : RawGuard A D) (C₁ C₂ : RawCmd A D) : RawCmd A D
| «while» (G : RawGuard A D) (C : RawCmd A D) : RawCmd A D
deriving DecidableEq, Repr

namespace RawCmd

variable {A D : Type}
variable [RelationNames A] [Domain D]

/- Relation names assigned by a raw command. -/
def assignedSymbols : RawCmd A D → Finset A
| .skip => ∅
| .assign X _ => {X}
| .assignEmpty X => {X}
| .seq C₁ C₂ => C₁.assignedSymbols ∪ C₂.assignedSymbols
| .ite _ C₁ C₂ => C₁.assignedSymbols ∪ C₂.assignedSymbols
| .«while» _ C => C.assignedSymbols

/- Relation names read or assigned by a raw command. -/
def symbols : RawCmd A D → Finset A
| .skip => ∅
| .assign X e => {X} ∪ e.symbols
| .assignEmpty X => {X}
| .seq C₁ C₂ => C₁.symbols ∪ C₂.symbols
| .ite G C₁ C₂ => G.symbols ∪ C₁.symbols ∪ C₂.symbols
| .«while» G C => G.symbols ∪ C.symbols

/- Domain constants occurring in a raw command. -/
def constants : RawCmd A D → Finset D
| .skip => ∅
| .assign _ e => e.constants
| .assignEmpty _ => ∅
| .seq C₁ C₂ => C₁.constants ∪ C₂.constants
| .ite G C₁ C₂ => G.constants ∪ C₁.constants ∪ C₂.constants
| .«while» G C => G.constants ∪ C.constants

/- Sequential composition of a raw command list. -/
def seqList : List (RawCmd A D) → RawCmd A D
| [] => .skip
| C :: Cs => .seq C (seqList Cs)

/- Check a raw assignment against a schema. -/
def assign?
    (Γ : UnnamedSchema A)
    (X : A)
    (e : RawRAExpr A D) :
    Option (Cmd D Γ) :=
  if hX : X ∈ Γ.syms then
    let XΓ : Γ.syms := ⟨X, hX⟩
    match hE : e.arity? Γ with
    | some n =>
        if hAr : n = Γ.arity XΓ then
          some
            (.assign XΓ
              ({ expr := e, wf := by
                  rw [← hAr]
                  exact hE } :
                RAExpr D Γ (Γ.arity XΓ)))
        else
          none
    | none => none
  else
    none

/- Check an empty-relation assignment against a schema. -/
def assignEmpty?
    (Γ : UnnamedSchema A)
    (X : A) :
    Option (Cmd D Γ) :=
  if hX : X ∈ Γ.syms then
    let XΓ : Γ.syms := ⟨X, hX⟩
    some (.assign XΓ (RAExpr.empty (Γ.arity XΓ)))
  else
    none

/- Check a raw command against a schema. -/
def toCmd?
    (Γ : UnnamedSchema A) :
    RawCmd A D → Option (Cmd D Γ)
| .skip => some .skip
| .assign X e => assign? Γ X e
| .assignEmpty X => assignEmpty? Γ X
| .seq C₁ C₂ =>
    match toCmd? Γ C₁, toCmd? Γ C₂ with
    | some C₁', some C₂' => some (.seq C₁' C₂')
    | _, _ => none
| .ite G C₁ C₂ =>
    match G.toGuard? Γ, toCmd? Γ C₁, toCmd? Γ C₂ with
    | some G', some C₁', some C₂' =>
        some (.ite G' C₁' C₂')
    | _, _, _ => none
| .«while» G C =>
    match G.toGuard? Γ, toCmd? Γ C with
    | some G', some C' => some (.while G' C')
    | _, _ => none

/- Checked conversion from raw syntax to a typed command. -/
def toCmd
    {Γ : UnnamedSchema A}
    (C : RawCmd A D)
    (h : (C.toCmd? Γ).isSome = Bool.true := by decide) :
    Cmd D Γ :=
  match hC : C.toCmd? Γ with
  | some C' => C'
  | none =>
      have hFalse : False := by
        rw [hC] at h
        contradiction
      False.elim hFalse

@[simp] private theorem rawRAExpr_heq
    {Γ : UnnamedSchema A}
    {m n : Nat}
    {e : RawRAExpr A D}
    (hm : e.arity? Γ = some m)
    (hn : e.arity? Γ = some n) :
    HEq
      ({ expr := e, wf := hm } : RAExpr D Γ m)
      ({ expr := e, wf := hn } : RAExpr D Γ n) := by
  have hmn : m = n := by
    rw [hm] at hn
    injection hn
  subst n
  simp

/-
  Checking the raw form of a typed assignment recovers it.
-/
theorem toCmd?_assign_expr
    {Γ : UnnamedSchema A}
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    (RawCmd.assign X.1 e.expr).toCmd? Γ =
      some (Cmd.assign X e) := by
  cases X with
  | mk X hX =>
      cases e with
      | mk expr wf =>
          change
            assign? Γ X expr =
              some
                (Cmd.assign ⟨X, hX⟩
                  ({ expr := expr, wf := wf } :
                    RAExpr D Γ (Γ.arity ⟨X, hX⟩)))
          unfold assign?
          split <;> aesop

/-
  Checking an untagged empty assignment recovers typed
  empty assignment.
-/
theorem toCmd?_assign_empty
    {Γ : UnnamedSchema A}
    (X : Γ.syms) :
    (RawCmd.assignEmpty (D := D) X.1).toCmd? Γ =
      some (Cmd.assign X (RAExpr.empty (Γ.arity X))) := by
  cases X with
  | mk X hX =>
      change
        assignEmpty? Γ X =
          some
            (Cmd.assign ⟨X, hX⟩
              (RAExpr.empty (Γ.arity ⟨X, hX⟩)))
      unfold assignEmpty?
      split <;> aesop

end RawCmd

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Erase a typed command to its raw syntax. -/
def toRaw :
    Cmd D Γ → RawCmd A D
| .skip => .skip
| .assign X e => .assign X.1 e.expr
| .seq C₁ C₂ => .seq C₁.toRaw C₂.toRaw
| .ite G C₁ C₂ =>
    .ite G.toRaw C₁.toRaw C₂.toRaw
| .«while» G C => .«while» G.toRaw C.toRaw

/- Checking a typed command's raw syntax recovers it. -/
@[simp] theorem toRaw_toCmd?
    (C : Cmd D Γ) :
    C.toRaw.toCmd? Γ = some C := by
  induction C with
  | skip =>
      rfl
  | assign X e =>
      exact RawCmd.toCmd?_assign_expr X e
  | seq C₁ C₂ h₁ h₂ =>
      simp [toRaw, RawCmd.toCmd?, h₁, h₂]
  | ite G C₁ C₂ h₁ h₂ =>
      simp [toRaw, RawCmd.toCmd?, h₁, h₂]
  | «while» G C h =>
      simp [toRaw, RawCmd.toCmd?, h]

/- Equal raw syntax gives equal typed commands. -/
theorem eq_of_toRaw_eq
    {C₁ C₂ : Cmd D Γ}
    (hRaw : C₁.toRaw = C₂.toRaw) :
    C₁ = C₂ := by
  have h₁ := toRaw_toCmd? C₁
  have h₂ := toRaw_toCmd? C₂
  rw [hRaw] at h₁
  rw [h₂] at h₁
  injection h₁ with hEq
  exact hEq.symm

end Cmd

end Whiel
