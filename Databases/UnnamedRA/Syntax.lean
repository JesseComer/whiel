-- Author: Jesse Comer
import Databases.Core.UnnamedSchema

/-
  This file specifies the syntax and well-formedness layer
  for unnamed relational algebra.

  Key definitions include:
    * `Sel`
    * `RawRAExpr`
    * `RawRAExpr.arity?`
    * `RAExpr`

  Key theorems include:
    * `RawRAExpr.symbols_subset_of_schema`
    * `RawRAExpr.wf_extension_of_eq`
    * `RawRAExpr.arity?_restrict_eq`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Selection Conditions
------------------------------------------------------------

/- Boolean selection conditions over tuple coordinates. -/
inductive Sel (D : Type) [Domain D] : Type
| eqIdx (i j : Nat)
| eqConst (i : Nat) (c : D)
| and (s₁ s₂ : Sel D)
| or (s₁ s₂ : Sel D)
| not (s : Sel D)
deriving DecidableEq, Repr

namespace Sel

variable {D : Type} [Domain D]

/- Computing the largest index occurring in a `Sel`. -/
def arityReq : Sel D → Nat
| .eqIdx i j => Nat.max i j
| .eqConst i _ => i
| .and s₁ s₂ =>
    Nat.max (arityReq s₁) (arityReq s₂)
| .or s₁ s₂ =>
    Nat.max (arityReq s₁) (arityReq s₂)
| .not s => arityReq s

/- Constants occurring in a `Sel`. -/
def constants : Sel D → Finset D
| .eqIdx _ _ => ∅
| .eqConst _ c => {c}
| .and s₁ s₂ => constants s₁ ∪ constants s₂
| .or s₁ s₂ => constants s₁ ∪ constants s₂
| .not s => constants s

end Sel

------------------------------------------------------------
-- Raw Expressions
------------------------------------------------------------

/-
  Raw relational algebra expressions may be ill-formed;
  well-formedness requires a proof that `arity?` returns
  `some n` for `n : Nat`.
-/
inductive RawRAExpr
    (A D : Type)
    [RelationNames A]
    [Domain D] : Type
| top
| empty (n : Nat)
| rel (X : A)
| single (d : D)
| select (φ : Sel D) (e : RawRAExpr A D)
| proj (idxs : List Nat) (e : RawRAExpr A D)
| prod (e₁ e₂ : RawRAExpr A D)
| union (e₁ e₂ : RawRAExpr A D)
| diff (e₁ e₂ : RawRAExpr A D)
deriving DecidableEq, Repr

namespace RawRAExpr

variable {A D : Type} [RelationNames A] [Domain D]

/- Coercion from relation names to `RawRAExpr`. -/
instance : Coe A (RawRAExpr A D) where
  coe X := .rel X

/- Relation names occurring in a `RawRAExpr`. -/
def symbols : RawRAExpr A D → Finset A
| .top => ∅
| .empty _ => ∅
| .rel X => {X}
| .single _ => ∅
| .select _ e => symbols e
| .proj _ e => symbols e
| .prod e₁ e₂ => symbols e₁ ∪ symbols e₂
| .union e₁ e₂ => symbols e₁ ∪ symbols e₂
| .diff e₁ e₂ => symbols e₁ ∪ symbols e₂

/- Constants occurring in a `RawRAExpr`. -/
def constants : RawRAExpr A D → Finset D
| .top => ∅
| .empty _ => ∅
| .rel _ => ∅
| .single d => {d}
| .select φ e => φ.constants ∪ constants e
| .proj _ e => constants e
| .prod e₁ e₂ => constants e₁ ∪ constants e₂
| .union e₁ e₂ => constants e₁ ∪ constants e₂
| .diff e₁ e₂ => constants e₁ ∪ constants e₂

/-
  Function taking a `RawRAExpr` `e` as input and returning
  `some n` if `e` is well-formed and has arity `n`, and
  `none` otherwise.
-/
def arity? (Γ : UnnamedSchema A) :
    RawRAExpr A D → Option Nat
| .top => some 0
| .empty n => some n
| .rel X => Γ.arity? X
| .single _ => some 1
| .select φ e =>
    match arity? Γ e with
    | some n =>
        if decide (φ.arityReq < n) then
          some n
        else
          none
    | none => none
| .proj idxs e =>
    match arity? Γ e with
    | some n =>
        if decide (∀ i ∈ idxs, i < n) then
          some idxs.length
        else
          none
    | none => none
| .prod e₁ e₂ =>
    match arity? Γ e₁, arity? Γ e₂ with
    | some n, some m => some (n + m)
    | _, _ => none
| .union e₁ e₂ =>
    match arity? Γ e₁, arity? Γ e₂ with
    | some n, some m =>
        if decide (n = m) then
          some n
        else
          none
    | _, _ => none
| .diff e₁ e₂ =>
    match arity? Γ e₁, arity? Γ e₂ with
    | some n, some m =>
        if decide (n = m) then
          some n
        else
          none
    | _, _ => none

/-
  Well-formed raw expressions only mention symbols
  from the schema.
-/
theorem symbols_subset_of_schema
    {Γ : UnnamedSchema A}
    {e : RawRAExpr A D}
    {n : Nat}
    (hAr : e.arity? Γ = some n) :
    e.symbols ⊆ Γ.syms := by
  induction e generalizing n with
  | top =>
      intro x hx
      simp [symbols] at hx
  | empty m =>
      intro x hx
      simp [symbols] at hx
  | rel X =>
      have hX : X ∈ Γ.syms := by
        by_cases hmem : X ∈ Γ.syms
        · exact hmem
        · have : False := by
            simp [arity?, UnnamedSchema.arity?, hmem] at hAr
          exact False.elim this
      intro x hx
      have hx' : x = X := by
        simpa [symbols] using hx
      simpa [hx'] using hX
  | single d =>
      intro x hx
      simp [symbols] at hx
  | select φ e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [arity?, hE] at hAr
      | some m =>
          by_cases hReq : φ.arityReq < m
          · have hSub := ih hE
            intro x hx
            exact hSub (by simpa [symbols] using hx)
          · simp [arity?, hE, hReq] at hAr
  | proj idxs e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [arity?, hE] at hAr
      | some m =>
          by_cases hOk : ∀ i ∈ idxs, i < m
          · have hSub := ih hE
            intro x hx
            exact hSub (by simpa [symbols] using hx)
          · simp [arity?, hE, hOk] at hAr
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              have hSub₁ := ih₁ h₁
              have hSub₂ := ih₂ h₂
              intro x hx
              have hMem := Finset.mem_union.mp hx
              cases hMem with
              | inl hx₁ => exact hSub₁ hx₁
              | inr hx₂ => exact hSub₂ hx₂
  | union e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              have hSub₁ := ih₁ h₁
              have hSub₂ := ih₂ h₂
              intro x hx
              have hMem := Finset.mem_union.mp hx
              cases hMem with
              | inl hx₁ => exact hSub₁ hx₁
              | inr hx₂ => exact hSub₂ hx₂
  | diff e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              have hSub₁ := ih₁ h₁
              have hSub₂ := ih₂ h₂
              intro x hx
              have hMem := Finset.mem_union.mp hx
              cases hMem with
              | inl hx₁ => exact hSub₁ hx₁
              | inr hx₂ => exact hSub₂ hx₂

/-
  If `Δ` extends `Γ`, any expression well-formed in `Γ`
  is well-formed in `Δ` with the same arity.
-/
theorem wf_extension_of_eq
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    {e : RawRAExpr A D}
    {n : Nat}
    (hAr : e.arity? Γ = some n) :
    e.arity? Δ = some n := by
  induction e generalizing n with
  | top =>
      simpa [arity?] using hAr
  | empty m =>
      simpa [arity?] using hAr
  | rel X =>
      by_cases hX : X ∈ Γ.syms
      · have hArΓ : Γ.arity ⟨X, hX⟩ = n := by
          have hAr' :
              some (Γ.arity ⟨X, hX⟩) = some n := by
            simpa
              [arity?, UnnamedSchema.arity?, hX]
              using hAr
          exact Option.some.inj hAr'
        have hArΔ :
            Δ.arity? X = some (Γ.arity ⟨X, hX⟩) :=
          hExt.2 ⟨X, hX⟩
        calc
          arity? Δ (.rel X)
              = Δ.arity? X := by
                simp [arity?]
          _ = some (Γ.arity ⟨X, hX⟩) := hArΔ
          _ = some n := by
                simp [hArΓ]
      · exfalso
        simp [arity?, UnnamedSchema.arity?, hX] at hAr
  | single d =>
      simpa [arity?] using hAr
  | select φ e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [arity?, hE] at hAr
      | some m =>
          by_cases hReq : φ.arityReq < m
          · have hm : m = n := by
              simpa [arity?, hE, hReq] using hAr
            have hEΔ : e.arity? Δ = some m := ih hE
            have hSel :
                arity? Δ (.select φ e) = some m := by
              simp [arity?, hEΔ, hReq]
            calc
              arity? Δ (.select φ e) = some m := hSel
              _ = some n := by
                    simp [hm]
          · simp [arity?, hE, hReq] at hAr
  | proj idxs e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [arity?, hE] at hAr
      | some m =>
          by_cases hOk : ∀ i ∈ idxs, i < m
          · have hm : idxs.length = n := by
              have hPair :
                  (∀ i ∈ idxs, i < m)
                    ∧ idxs.length = n := by
                simpa [arity?, hE, hOk] using hAr
              exact hPair.2
            have hEΔ : e.arity? Δ = some m := ih hE
            have hDec :
                decide (∀ i ∈ idxs, i < m) = true := by
              exact decide_eq_true hOk
            have hProj :
                arity? Δ (.proj idxs e)
                  = some idxs.length := by
              simp [arity?, hEΔ, hDec]
            calc
              arity? Δ (.proj idxs e)
                  = some idxs.length := hProj
              _ = some n := by
                    simp [hm]
          · simp [arity?, hE, hOk] at hAr
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              have hsum : n₁ + n₂ = n := by
                simpa [arity?, h₁, h₂] using hAr
              have h₁Δ :
                  e₁.arity? Δ = some n₁ := ih₁ h₁
              have h₂Δ :
                  e₂.arity? Δ = some n₂ := ih₂ h₂
              simp [arity?, h₁Δ, h₂Δ, hsum]
  | union e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hm : n₁ = n := by
                  simpa [arity?, h₁, h₂, hEq] using hAr
                have h₁Δ :
                    e₁.arity? Δ = some n₁ := ih₁ h₁
                have h₂Δ :
                    e₂.arity? Δ = some n₂ := ih₂ h₂
                have hUnion :
                    arity? Δ (.union e₁ e₂)
                      = some n₁ := by
                  simp [arity?, h₁Δ, h₂Δ, hEq]
                calc
                  arity? Δ (.union e₁ e₂)
                      = some n₁ := hUnion
                  _ = some n := by
                        simp [hm]
              · simp [arity?, h₁, h₂, hEq] at hAr
  | diff e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hm : n₁ = n := by
                  simpa [arity?, h₁, h₂, hEq] using hAr
                have h₁Δ :
                    e₁.arity? Δ = some n₁ := ih₁ h₁
                have h₂Δ :
                    e₂.arity? Δ = some n₂ := ih₂ h₂
                have hDiff :
                    arity? Δ (.diff e₁ e₂)
                      = some n₁ := by
                  simp [arity?, h₁Δ, h₂Δ, hEq]
                calc
                  arity? Δ (.diff e₁ e₂)
                      = some n₁ := hDiff
                  _ = some n := by
                        simp [hm]
              · simp [arity?, h₁, h₂, hEq] at hAr

/-
  Strong form: if `e` has some arity in `Γ`, then
  the arity result is unchanged in any extension `Δ`.
-/
theorem wf_extension
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    {e : RawRAExpr A D}
    (hWf : ∃ n, e.arity? Γ = some n) :
    e.arity? Δ = e.arity? Γ := by
  rcases hWf with ⟨n, hAr⟩
  have hArΔ :
      e.arity? Δ = some n :=
    wf_extension_of_eq hExt hAr
  simpa [hAr] using hArΔ

/-
  Restricting `Γ` to any symbol set containing
  `e.symbols` preserves `e`'s arity check.
-/
theorem arity?_restrict_eq
    {Γ : UnnamedSchema A}
    (e : RawRAExpr A D) :
    ∀ {S : Finset A},
      (hSΓ : S ⊆ Γ.syms) →
      e.symbols ⊆ S →
      e.arity? (UnnamedSchema.restrict Γ S hSΓ) =
        e.arity? Γ := by
  induction e with
  | top =>
      intro S hSΓ hSym
      simp [arity?]
  | empty n =>
      intro S hSΓ hSym
      simp [arity?]
  | rel X =>
      intro S hSΓ hSym
      have hXS : X ∈ S := hSym (by simp [symbols])
      have hXΓ : X ∈ Γ.syms := hSΓ hXS
      change
        UnnamedSchema.arity?
          (UnnamedSchema.restrict Γ S hSΓ) X =
            UnnamedSchema.arity? Γ X
      have hRestr :
          X ∈
            (UnnamedSchema.restrict Γ S hSΓ).syms := by
        simpa [UnnamedSchema.restrict] using hXS
      rw [show
          UnnamedSchema.arity?
            (UnnamedSchema.restrict Γ S hSΓ) X =
              some
                ((UnnamedSchema.restrict Γ S hSΓ).arity
                  ⟨X, hRestr⟩) by
            simp [UnnamedSchema.arity?, hRestr]]
      rw [show
          UnnamedSchema.arity? Γ X =
            some (Γ.arity ⟨X, hXΓ⟩) by
            simp [UnnamedSchema.arity?, hXΓ]]
      unfold UnnamedSchema.restrict
      rfl
  | single d =>
      intro S hSΓ hSym
      simp [arity?]
  | select φ e ih =>
      intro S hSΓ hSym
      have hSub : e.symbols ⊆ S := by
        intro X hX
        exact hSym (by simpa [symbols] using hX)
      have hEq :
          e.arity? (UnnamedSchema.restrict Γ S hSΓ) =
            e.arity? Γ := ih hSΓ hSub
      simp [arity?, hEq]
  | proj idxs e ih =>
      intro S hSΓ hSym
      have hSub : e.symbols ⊆ S := by
        intro X hX
        exact hSym (by simpa [symbols] using hX)
      have hEq :
          e.arity? (UnnamedSchema.restrict Γ S hSΓ) =
            e.arity? Γ := ih hSΓ hSub
      simp [arity?, hEq]
  | prod e₁ e₂ ih₁ ih₂ =>
      intro S hSΓ hSym
      have hSub₁ : e₁.symbols ⊆ S := by
        intro X hX
        exact hSym (Finset.mem_union.mpr (Or.inl hX))
      have hSub₂ : e₂.symbols ⊆ S := by
        intro X hX
        exact hSym (Finset.mem_union.mpr (Or.inr hX))
      simp [arity?, ih₁ hSΓ hSub₁, ih₂ hSΓ hSub₂]
  | union e₁ e₂ ih₁ ih₂ =>
      intro S hSΓ hSym
      have hSub₁ : e₁.symbols ⊆ S := by
        intro X hX
        exact hSym (Finset.mem_union.mpr (Or.inl hX))
      have hSub₂ : e₂.symbols ⊆ S := by
        intro X hX
        exact hSym (Finset.mem_union.mpr (Or.inr hX))
      simp [arity?, ih₁ hSΓ hSub₁, ih₂ hSΓ hSub₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      intro S hSΓ hSym
      have hSub₁ : e₁.symbols ⊆ S := by
        intro X hX
        exact hSym (Finset.mem_union.mpr (Or.inl hX))
      have hSub₂ : e₂.symbols ⊆ S := by
        intro X hX
        exact hSym (Finset.mem_union.mpr (Or.inr hX))
      simp [arity?, ih₁ hSΓ hSub₁, ih₂ hSΓ hSub₂]

end RawRAExpr

------------------------------------------------------------
-- Well-Formed Expressions
------------------------------------------------------------

/- Well-formed RA expressions with known output arity. -/
structure RAExpr
    {A : Type}
    {_ : RelationNames A}
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) (n : Nat) where
  expr : RawRAExpr A D
  wf : expr.arity? Γ = some n

namespace RAExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ Δ : UnnamedSchema A} {n : Nat}

/- Relation names occurring in an `RAExpr`. -/
def symbols (e : RAExpr D Γ n) : Finset A :=
  e.expr.symbols

/- Constants occurring in an `RAExpr`. -/
def constants (e : RAExpr D Γ n) : Finset D :=
  e.expr.constants

/-
  Well-formed expressions only use symbols from their
  schema.
-/
theorem symbols_subset
    (e : RAExpr D Γ n) :
    e.symbols ⊆ Γ.syms :=
  RawRAExpr.symbols_subset_of_schema e.wf

/- Transport an expression across output-arity equality. -/
def castArity
    {m n : Nat}
    (h : m = n)
    (e : RAExpr D Γ n) :
    RAExpr D Γ m where
  expr := e.expr
  wf := by
    rw [h]
    exact e.wf

end RAExpr

------------------------------------------------------------
-- Constructors
------------------------------------------------------------

namespace RAExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/- The nullary singleton relation. -/
def top :
    RAExpr D Γ 0 where
  expr := .top
  wf := by
    simp [RawRAExpr.arity?]

/- The empty relation at a fixed arity. -/
def empty
    (n : Nat) :
    RAExpr D Γ n where
  expr := .empty n
  wf := by
    simp [RawRAExpr.arity?]

/- The relation denoted by a schema symbol. -/
def rel
    (X : Γ.syms) :
    RAExpr D Γ (Γ.arity X) where
  expr := .rel X.1
  wf := by
    simp [RawRAExpr.arity?, UnnamedSchema.arity?, X.2]

/-
  The relation `Y`, typed at `X`'s arity when those arities
  are propositionally equal.
-/
def relAs
    (X Y : Γ.syms)
    (hAr : Γ.arity X = Γ.arity Y) :
    RAExpr D Γ (Γ.arity X) :=
  castArity hAr (rel Y)

/- A unary singleton constant relation. -/
def single
    (d : D) :
    RAExpr D Γ 1 where
  expr := .single d
  wf := by
    simp [RawRAExpr.arity?]

/- Selection with an explicit arity-bound proof. -/
def select
    {n : Nat}
    (φ : Sel D)
    (e : RAExpr D Γ n)
    (hReq : φ.arityReq < n) :
    RAExpr D Γ n where
  expr := .select φ e.expr
  wf := by
    simp [RawRAExpr.arity?, e.wf, hReq]

/- Projection with explicit index-bound proofs. -/
def proj
    {n : Nat}
    (idxs : List Nat)
    (e : RAExpr D Γ n)
    (hIdx : ∀ i, i ∈ idxs → i < n) :
    RAExpr D Γ idxs.length where
  expr := .proj idxs e.expr
  wf := by
    rw [RawRAExpr.arity?, e.wf]
    have hDec :
        decide (∀ i ∈ idxs, i < n) = true :=
      decide_eq_true hIdx
    simp [hDec]

/- Relational product. -/
def prod
    {n m : Nat}
    (e₁ : RAExpr D Γ n)
    (e₂ : RAExpr D Γ m) :
    RAExpr D Γ (n + m) where
  expr := .prod e₁.expr e₂.expr
  wf := by
    simp [RawRAExpr.arity?, e₁.wf, e₂.wf]

/- Same-arity relational union. -/
def union
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    RAExpr D Γ n where
  expr := .union e₁.expr e₂.expr
  wf := by
    simp [RawRAExpr.arity?, e₁.wf, e₂.wf]

/- Same-arity relational difference. -/
def diff
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    RAExpr D Γ n where
  expr := .diff e₁.expr e₂.expr
  wf := by
    simp [RawRAExpr.arity?, e₁.wf, e₂.wf]

end RAExpr

------------------------------------------------------------
-- Support Schemas and Retyping
------------------------------------------------------------

namespace RAExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ Δ : UnnamedSchema A} {n : Nat}

/-
  Reinterpret a typed expression over an extending
  schema without changing its output arity.
-/
def onExtension
    (hExt : Δ.extensionOf Γ)
    (e : RAExpr D Γ n) :
    RAExpr D Δ n :=
{
  expr := e.expr
  wf := RawRAExpr.wf_extension_of_eq hExt e.wf
}

/-
  Well-formedness is preserved under schema extension.
-/
theorem wf_mono_extension
    (hExt : Δ.extensionOf Γ)
    (e : RAExpr D Γ n) :
    e.expr.arity? Δ = some n :=
  RawRAExpr.wf_extension_of_eq hExt e.wf

/-
  The smallest restriction of `Γ` containing
  all symbols occurring in `e`.
-/
def supportSchema
    (e : RAExpr D Γ n) : UnnamedSchema A :=
  UnnamedSchema.restrict Γ e.symbols e.symbols_subset

@[simp] theorem supportSchema_syms
    (e : RAExpr D Γ n) :
    e.supportSchema.syms = e.symbols := rfl

/-
  The support schema is a restriction of the
  original schema.
-/
theorem extension_supportSchema
    (e : RAExpr D Γ n) :
    Γ.extensionOf e.supportSchema := by
  simpa [supportSchema] using
    UnnamedSchema.extensionOf_restrict
      Γ e.symbols e.symbols_subset

/-
  Re-type `e` over its support schema.
-/
def onSupport
    (e : RAExpr D Γ n) :
    RAExpr D e.supportSchema n :=
{
  expr := e.expr
  wf := by
    have hEq :
        e.expr.arity? e.supportSchema =
          e.expr.arity? Γ := by
      simpa [supportSchema] using
        (RawRAExpr.arity?_restrict_eq
          (Γ := Γ) e.expr
          (S := e.symbols)
          e.symbols_subset
          (by intro X hX; exact hX))
    simpa [hEq] using e.wf
}

/-
  Minimality: any restriction carrier set in `Γ`
  that contains `e.symbols` also contains
  `e.supportSchema.syms`.
-/
theorem supportSchema_min
    (e : RAExpr D Γ n)
    {S : Finset A}
    (_ : S ⊆ Γ.syms)
    (hContain : e.symbols ⊆ S) :
    e.supportSchema.syms ⊆ S := by
  simpa [supportSchema] using hContain

end RAExpr
