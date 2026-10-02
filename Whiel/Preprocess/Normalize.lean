-- Author: Jesse Comer
import Whiel.Preprocess.Clean
import Whiel.Preprocess.Merge
import Whiel.Preprocess.Flatten

/-
  The normalizer of the generic Whiel preprocessor.

  Normalization applies the three loop-removing operations
  bottom-up. It is a direct structural recursion on the
  command, threading a counter of the next free flag
  identifier, and it is total on all of Whiel: every command
  has an output and none is refused.

  The counter counts from a seed: the input schema's first
  free flag identifier, which is zero on every
  `RawIndexZero` input. Computing that seed is a `Finset`
  fold, and it is the one finite-set computation anywhere
  in the transformation. `FlagSupply` carries its value
  together with the bound that makes every larger
  identifier fresh, and `normalizeAux` takes the supply as
  a parameter, so the fold is evaluated once, at
  `normalize`, and never at a draw site: every drawn
  identifier is the plain arithmetic `s.seed + j`, and
  freshness never needs a hypothesis.

  Key definitions include:
    * `Whiel.Preprocess.flagBudget`
    * `Whiel.Preprocess.twoLoopApplications`
    * `Whiel.Preprocess.NormResult`
    * `Whiel.Preprocess.NormResult.clean`
    * `Whiel.Preprocess.FlagSupply`
    * `Whiel.Preprocess.normalizeAux`
    * `Whiel.Preprocess.normalize`

  Correctness is proven by:
    * `Whiel.Preprocess.normalizeAux_ids`
    * `Whiel.Preprocess.normalizeAux_footprint`
    * `Whiel.Preprocess.normalize_equivMod`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Source-Level Tests
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Syntactic equality of two guard terms. -/
def guardSame (G₁ G₂ : Guard D Γ) : Bool :=
  decide (G₁.toRaw = G₂.toRaw)

/- Syntactically equal guard terms are equal. -/
theorem eq_of_guardSame
    {G₁ G₂ : Guard D Γ}
    (hSame : guardSame G₁ G₂ = true) :
    G₁ = G₂ := by
  have hRaw : G₁.toRaw = G₂.toRaw :=
    of_decide_eq_true hSame
  have hOne : G₁.toRaw.toGuard? Γ = some G₁ :=
    Guard.toRaw_toGuard? G₁
  rw [hRaw, Guard.toRaw_toGuard? G₂] at hOne
  exact (Option.some.inj hOne).symm

/-
  The idempotent-nesting test: the source body is a loop
  whose guard term is syntactically the outer one.
-/
def idemCheck (G : Guard D Γ) : Cmd D Γ → Bool
| .skip => false
| .assign _ _ => false
| .seq _ _ => false
| .ite _ _ _ => false
| .«while» G' _ => guardSame G' G

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flag Budget
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The number of flag identifiers the recursion draws,
  computed first and by the same case analysis, in the same
  order.
-/
def flagBudget : Cmd D Γ → Nat
| .skip => 0
| .assign _ _ => 0
| .seq C₁ C₂ =>
    flagBudget C₁ + flagBudget C₂ +
      (if LoopFree C₁ then 0
       else if LoopFree C₂ then 0
       else if independentCheck C₁ C₂ then 0
       else 2)
| .ite _ C₁ C₂ =>
    flagBudget C₁ + flagBudget C₂ +
      (if LoopFree C₁ then
         (if LoopFree C₂ then 0 else 1)
       else 1)
| .«while» G C₀ =>
    flagBudget C₀ +
      (if idemCheck G C₀ then 0
       else if LoopFree C₀ then 0
       else 1)

/- Loop-free code draws no flag. -/
theorem flagBudget_eq_zero_of_loopFree
    {C : Cmd D Γ}
    (hFree : LoopFree C) :
    flagBudget C = 0 := by
  induction C with
  | skip => rfl
  | assign X e => rfl
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases (loopFree_seq_iff C₁ C₂).mp hFree with
        ⟨h₁, h₂⟩
      simp [flagBudget, ih₁ h₁, ih₂ h₂, h₁]
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases (loopFree_ite_iff G C₁ C₂).mp hFree with
        ⟨h₁, h₂⟩
      simp [flagBudget, ih₁ h₁, ih₂ h₂, h₁, h₂]
  | «while» G C₀ ih =>
      exact absurd hFree (not_loopFree_while G C₀)

/-
  The conditionals of a command with a loop in a branch:
  the second summand of the note's bound on the budget.
-/
def branchingLoops : Cmd D Γ → Nat
| .skip => 0
| .assign _ _ => 0
| .seq C₁ C₂ => branchingLoops C₁ + branchingLoops C₂
| .ite _ C₁ C₂ =>
    branchingLoops C₁ + branchingLoops C₂ +
      (if LoopFree C₁ then
         (if LoopFree C₂ then 0 else 1)
       else 1)
| .«while» _ C₀ => branchingLoops C₀

/- Loop-free code has no branching loop. -/
theorem branchingLoops_eq_zero_of_loopFree
    {C : Cmd D Γ}
    (hFree : LoopFree C) :
    branchingLoops C = 0 := by
  induction C with
  | skip => rfl
  | assign X e => rfl
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases (loopFree_seq_iff C₁ C₂).mp hFree with
        ⟨h₁, h₂⟩
      simp [branchingLoops, ih₁ h₁, ih₂ h₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases (loopFree_ite_iff G C₁ C₂).mp hFree with
        ⟨h₁, h₂⟩
      simp [branchingLoops, ih₁ h₁, ih₂ h₂, h₁, h₂]
  | «while» G C₀ ih =>
      exact absurd hFree (not_loopFree_while G C₀)

/-
  The budget bound with its slack: a command that contains
  a loop spends at least two of its allowance on that loop.
-/
theorem flagBudget_bound
    (C : Cmd D Γ) :
    (loops C = 0 → flagBudget C = 0) ∧
      (0 < loops C →
        flagBudget C + 2 ≤
          2 * loops C + branchingLoops C) := by
  induction C with
  | skip =>
      exact ⟨fun _ => rfl, fun h => by simp [loops] at h⟩
  | assign X e =>
      exact ⟨fun _ => rfl, fun h => by simp [loops] at h⟩
  | seq C₁ C₂ ih₁ ih₂ =>
      constructor
      · intro hZero
        have h₁ : loops C₁ = 0 := by
          simp [loops] at hZero; omega
        have h₂ : loops C₂ = 0 := by
          simp [loops] at hZero; omega
        have hFree₁ : LoopFree C₁ := h₁
        simp [flagBudget, ih₁.1 h₁, ih₂.1 h₂, hFree₁]
      · intro hPos
        by_cases hOne : loops C₁ = 0
        · have hFree₁ : LoopFree C₁ := hOne
          have hPos₂ : 0 < loops C₂ := by
            simp [loops, hOne] at hPos ⊢; omega
          have hB₂ := ih₂.2 hPos₂
          have hB₁ := ih₁.1 hOne
          have hBr₁ : branchingLoops C₁ = 0 := by
            exact branchingLoops_eq_zero_of_loopFree
              hFree₁
          simp only [flagBudget, loops, branchingLoops,
            if_pos hFree₁, hB₁]
          omega
        · have hPos₁ : 0 < loops C₁ := by omega
          have hB₁ := ih₁.2 hPos₁
          by_cases hTwo : loops C₂ = 0
          · have hFree₂ : LoopFree C₂ := hTwo
            have hB₂ := ih₂.1 hTwo
            have hBr₂ : branchingLoops C₂ = 0 :=
              branchingLoops_eq_zero_of_loopFree hFree₂
            have hFree₁ : ¬ LoopFree C₁ := by
              intro h; exact hOne h
            simp only [flagBudget, loops, branchingLoops,
              if_neg hFree₁, if_pos hFree₂, hB₂]
            omega
          · have hPos₂ : 0 < loops C₂ := by omega
            have hB₂ := ih₂.2 hPos₂
            have hFree₁ : ¬ LoopFree C₁ := fun h => hOne h
            have hFree₂ : ¬ LoopFree C₂ := fun h => hTwo h
            simp only [flagBudget, loops, branchingLoops,
              if_neg hFree₁, if_neg hFree₂]
            split <;> omega
  | ite G C₁ C₂ ih₁ ih₂ =>
      constructor
      · intro hZero
        have h₁ : loops C₁ = 0 := by
          simp [loops] at hZero; omega
        have h₂ : loops C₂ = 0 := by
          simp [loops] at hZero; omega
        have hFree₁ : LoopFree C₁ := h₁
        have hFree₂ : LoopFree C₂ := h₂
        simp [flagBudget, ih₁.1 h₁, ih₂.1 h₂, hFree₁,
          hFree₂]
      · intro hPos
        by_cases hOne : loops C₁ = 0
        · have hFree₁ : LoopFree C₁ := hOne
          have hPos₂ : 0 < loops C₂ := by
            simp [loops, hOne] at hPos ⊢; omega
          have hFree₂ : ¬ LoopFree C₂ := by
            intro h
            have : loops C₂ = 0 := h
            omega
          have hB₂ := ih₂.2 hPos₂
          have hBr₁ : branchingLoops C₁ = 0 :=
            branchingLoops_eq_zero_of_loopFree hFree₁
          simp only [flagBudget, loops, branchingLoops,
            if_pos hFree₁, if_neg hFree₂, ih₁.1 hOne]
          omega
        · have hPos₁ : 0 < loops C₁ := by omega
          have hFree₁ : ¬ LoopFree C₁ := fun h => hOne h
          have hB₁ := ih₁.2 hPos₁
          by_cases hTwo : loops C₂ = 0
          · have hFree₂ : LoopFree C₂ := hTwo
            have hBr₂ : branchingLoops C₂ = 0 :=
              branchingLoops_eq_zero_of_loopFree hFree₂
            simp only [flagBudget, loops, branchingLoops,
              if_neg hFree₁, ih₂.1 hTwo]
            omega
          · have hPos₂ : 0 < loops C₂ := by omega
            have hB₂ := ih₂.2 hPos₂
            simp only [flagBudget, loops, branchingLoops,
              if_neg hFree₁]
            omega
  | «while» G C₀ ih =>
      constructor
      · intro hZero
        simp [loops] at hZero
      · intro _
        by_cases hIdem : idemCheck G C₀ = true
        · by_cases hZero : loops C₀ = 0
          · simp only [flagBudget, loops,
              branchingLoops, if_pos hIdem, ih.1 hZero,
              hZero]
            omega
          · have hB := ih.2 (by omega)
            simp only [flagBudget, loops,
              branchingLoops, if_pos hIdem]
            omega
        · have hIdemF : idemCheck G C₀ = false := by
            cases h : idemCheck G C₀ with
            | false => rfl
            | true => exact absurd h hIdem
          by_cases hFree : LoopFree C₀
          · have hZero : loops C₀ = 0 := hFree
            simp only [flagBudget, loops,
              branchingLoops, hIdemF, if_pos hFree,
              Bool.false_eq_true, if_false, ih.1 hZero,
              hZero]
            omega
          · have hPos : 0 < loops C₀ := by
              rcases Nat.eq_zero_or_pos (loops C₀) with
                h | h
              · exact absurd h hFree
              · exact h
            have hB := ih.2 hPos
            simp only [flagBudget, loops,
              branchingLoops, hIdemF, if_neg hFree,
              Bool.false_eq_true, if_false]
            omega

/-
  Proposition "Loop count", the budget bound: the second
  clause.
-/
theorem flagBudget_le
    (C : Cmd D Γ) :
    flagBudget C ≤ 2 * loops C + branchingLoops C := by
  rcases Nat.eq_zero_or_pos (loops C) with hZero | hPos
  · rw [(flagBudget_bound C).1 hZero]
    exact Nat.zero_le _
  · have h := (flagBudget_bound C).2 hPos
    omega

/-
  The two-loop rule applications the recursion makes,
  counted first and by the same case analysis on the same
  source-level Booleans as the budget. A merge, a hoist and
  a flattening consume two loops exactly when both sides
  carry one; the idempotent clause is a flattening
  application, since it consumes the outer source loop
  together with the inner one.
-/
def twoLoopApplications : Cmd D Γ → Nat
| .skip => 0
| .assign _ _ => 0
| .seq C₁ C₂ =>
    twoLoopApplications C₁ + twoLoopApplications C₂ +
      (if LoopFree C₁ then 0
       else if LoopFree C₂ then 0
       else 1)
| .ite _ C₁ C₂ =>
    twoLoopApplications C₁ + twoLoopApplications C₂ +
      (if LoopFree C₁ then 0
       else if LoopFree C₂ then 0
       else 1)
| .«while» G C₀ =>
    twoLoopApplications C₀ +
      (if idemCheck G C₀ then 1
       else if LoopFree C₀ then 0
       else 1)

/- The idempotent clause fires only on a nested loop. -/
theorem loops_pos_of_idemCheck
    {G : Guard D Γ}
    {C₀ : Cmd D Γ}
    (hIdem : idemCheck G C₀ = true) :
    0 < loops C₀ := by
  cases C₀ with
  | skip => simp [idemCheck] at hIdem
  | assign X e => simp [idemCheck] at hIdem
  | seq C₁ C₂ => simp [idemCheck] at hIdem
  | ite G' C₁ C₂ => simp [idemCheck] at hIdem
  | «while» G' B => simp [loops]

/-
  Proposition "Loop count", the first clause: the count of
  two-loop applications. The count is over the source
  while-nodes, so the `while false` a base framed loop
  carries is intermediate data and not a source loop.
-/
theorem twoLoopApplications_eq
    (C : Cmd D Γ) :
    twoLoopApplications C = max (loops C - 1) 0 := by
  induction C with
  | skip => rfl
  | assign X e => rfl
  | seq C₁ C₂ ih₁ ih₂ =>
      by_cases h₁ : LoopFree C₁
      · have hZero₁ : loops C₁ = 0 := h₁
        simp only [twoLoopApplications, loops, if_pos h₁,
          ih₁, ih₂, hZero₁]
        omega
      · have hPos₁ : 0 < loops C₁ := by
          rcases Nat.eq_zero_or_pos (loops C₁) with h | h
          · exact absurd h h₁
          · exact h
        by_cases h₂ : LoopFree C₂
        · have hZero₂ : loops C₂ = 0 := h₂
          simp only [twoLoopApplications, loops,
            if_neg h₁, if_pos h₂, ih₁, ih₂, hZero₂]
          omega
        · have hPos₂ : 0 < loops C₂ := by
            rcases Nat.eq_zero_or_pos (loops C₂) with
              h | h
            · exact absurd h h₂
            · exact h
          simp only [twoLoopApplications, loops,
            if_neg h₁, if_neg h₂, ih₁, ih₂]
          omega
  | ite G C₁ C₂ ih₁ ih₂ =>
      by_cases h₁ : LoopFree C₁
      · have hZero₁ : loops C₁ = 0 := h₁
        simp only [twoLoopApplications, loops, if_pos h₁,
          ih₁, ih₂, hZero₁]
        omega
      · have hPos₁ : 0 < loops C₁ := by
          rcases Nat.eq_zero_or_pos (loops C₁) with h | h
          · exact absurd h h₁
          · exact h
        by_cases h₂ : LoopFree C₂
        · have hZero₂ : loops C₂ = 0 := h₂
          simp only [twoLoopApplications, loops,
            if_neg h₁, if_pos h₂, ih₁, ih₂, hZero₂]
          omega
        · have hPos₂ : 0 < loops C₂ := by
            rcases Nat.eq_zero_or_pos (loops C₂) with
              h | h
            · exact absurd h h₂
            · exact h
          simp only [twoLoopApplications, loops,
            if_neg h₁, if_neg h₂, ih₁, ih₂]
          omega
  | «while» G C₀ ih =>
      by_cases hIdem : idemCheck G C₀ = true
      · have hPos := loops_pos_of_idemCheck hIdem
        simp only [twoLoopApplications, loops,
          if_pos hIdem, ih]
        omega
      · have hIdemF : idemCheck G C₀ = false := by
          cases h : idemCheck G C₀ with
          | false => rfl
          | true => exact absurd h hIdem
        by_cases hFree : LoopFree C₀
        · have hZero : loops C₀ = 0 := hFree
          simp only [twoLoopApplications, loops, hIdemF,
            Bool.false_eq_true, if_false, if_pos hFree,
            ih, hZero]
          omega
        · have hPos : 0 < loops C₀ := by
            rcases Nat.eq_zero_or_pos (loops C₀) with
              h | h
            · exact absurd h hFree
            · exact h
          simp only [twoLoopApplications, loops, hIdemF,
            Bool.false_eq_true, if_false, if_neg hFree,
            ih]
          omega

end Preprocess

end Whiel

------------------------------------------------------------
-- The Flag Supply Of The Recursion
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

/- The identifiers `[a, a+n)`, in order. -/
def flagIds (a n : Nat) : List Nat :=
  (List.range n).map (fun j => a + j)

@[simp] theorem mem_flagIds_iff
    {a n x : Nat} :
    x ∈ flagIds a n ↔ a ≤ x ∧ x < a + n := by
  simp only [flagIds, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, hEq⟩
    omega
  · intro h
    exact ⟨x - a, by omega, by omega⟩

@[simp] theorem length_flagIds
    (a n : Nat) :
    (flagIds a n).length = n := by
  simp only [flagIds, List.length_map, List.length_range]

@[simp] theorem flagIds_zero (a : Nat) : flagIds a 0 = [] :=
  rfl

theorem flagIds_succ
    (a n : Nat) :
    flagIds a (n + 1) = flagIds a n ++ [a + n] := by
  simp only [flagIds, List.range_succ, List.map_append,
    List.map_cons, List.map_nil]

theorem flagIds_append
    (a n p : Nat) :
    flagIds a n ++ flagIds (a + n) p =
      flagIds a (n + p) := by
  induction p with
  | zero => simp
  | succ p ih =>
      have hSplit : n + (p + 1) = n + p + 1 := by omega
      have hShift : a + n + p = a + (n + p) := by omega
      rw [flagIds_succ (a + n) p, ← List.append_assoc, ih,
        hSplit, flagIds_succ a (n + p), hShift]

theorem flagIds_one (a : Nat) : flagIds a 1 = [a] := by
  rw [show (1 : Nat) = 0 + 1 from rfl, flagIds_succ]
  rfl

theorem flagIds_two
    (a : Nat) :
    flagIds a 2 = [a, a + 1] := by
  rw [show (2 : Nat) = 1 + 1 from rfl, flagIds_succ,
    flagIds_one]
  rfl

/- The names of a sublist of identifiers are a subset. -/
theorem mem_flagNames
    (Φ : List Nat)
    (X : ProgramNames) :
    X ∈ flagNames Φ ↔ ∃ i ∈ Φ, flagName i = X := by
  simp only [flagNames, List.mem_toFinset, List.mem_map]

theorem flagNames_subset
    {Φ₁ Φ₂ : List Nat}
    (hSub : Φ₁ ⊆ Φ₂) :
    flagNames Φ₁ ⊆ flagNames Φ₂ := by
  intro X hX
  rcases (mem_flagNames Φ₁ X).mp hX with ⟨i, hi, hEq⟩
  exact (mem_flagNames Φ₂ X).mpr ⟨i, hSub hi, hEq⟩

/- Adding identifiers extends the flag extension. -/
theorem flagExt_mono
    (Γ : UnnamedSchema ProgramNames)
    {Φ₁ Φ₂ : List Nat}
    (hSub : Φ₁ ⊆ Φ₂) :
    (flagExt Γ Φ₂).extensionOf (flagExt Γ Φ₁) := by
  have hSyms :
      (flagExt Γ Φ₁).syms ⊆ (flagExt Γ Φ₂).syms := by
    intro X hX
    rcases Finset.mem_union.mp hX with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _
        (flagNames_subset hSub h)
  refine ⟨hSyms, ?_⟩
  intro s
  have hMem : s.1 ∈ (flagExt Γ Φ₂).syms := hSyms s.2
  have hArity :
      (flagExt Γ Φ₂).arity? s.1 =
        some ((flagExt Γ Φ₂).arity ⟨s.1, hMem⟩) :=
    dif_pos hMem
  rw [hArity]
  rfl

theorem subsetAppendLeft
    (l₁ l₂ : List Nat) :
    l₁ ⊆ l₁ ++ l₂ := by
  intro x hx
  exact List.mem_append.mpr (Or.inl hx)

theorem subsetAppendRight
    (l₁ l₂ : List Nat) :
    l₂ ⊆ l₁ ++ l₂ := by
  intro x hx
  exact List.mem_append.mpr (Or.inr hx)

end Preprocess

end Whiel

------------------------------------------------------------
-- The Result Of The Recursion
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/-
  A framed loop together with the flag identifiers the
  recursion drew for it, in the order it drew them.
-/
structure NormResult
    (D : Type) [Domain D]
    (Γ : UnnamedSchema ProgramNames) : Type where
  ids : List Nat
  loop : Framed D (flagExt Γ ids)

/-
  The recursion's flag supply: a seed value at or above the
  input schema's first free flag identifier. The seed is
  the transformation's one finite-set computation, so its
  value is carried here and evaluated once, at `normalize`,
  rather than recomputed at every draw site.
-/
structure FlagSupply
    (Γ : UnnamedSchema ProgramNames) : Type where
  seed : Nat
  bound : flagSeed Γ ≤ seed

/- The supply the normalizer starts from. -/
def FlagSupply.initial
    (Γ : UnnamedSchema ProgramNames) :
    FlagSupply Γ where
  seed := flagSeed Γ
  bound := Nat.le_refl _

variable (s : FlagSupply Γ)

/- The identifier at a given offset from the supply. -/
def flagAt
    {Γ : UnnamedSchema ProgramNames}
    (s : FlagSupply Γ)
    (j : Nat) : Nat :=
  s.seed + j

/- Every drawn identifier is fresh for the input. -/
theorem flagName_flagAt_not_mem
    {Γ : UnnamedSchema ProgramNames}
    (s : FlagSupply Γ)
    (j : Nat) :
    flagName (flagAt s j) ∉ Γ.syms :=
  flagName_not_mem_of_flagSeed_le
    (Nat.le_trans s.bound (Nat.le_add_right _ _))

/- A drawn flag as a nullary symbol of the extension. -/
def drawnFlag
    {Γ : UnnamedSchema ProgramNames}
    (s : FlagSupply Γ)
    (Φ : List Nat)
    (j : Nat)
    (hMem : flagAt s j ∈ Φ) :
    FlagSym (flagExt Γ Φ) :=
  flagSymOf Γ Φ (flagAt s j) hMem
    (flagName_flagAt_not_mem s j)

/- The loop-free clause: the base framed loop. -/
def baseResult (C : Cmd D Γ) : NormResult D Γ where
  ids := []
  loop :=
    (Framed.base C).retagOn (flagExt_extensionOf Γ [])

/- The left sub-result read over the common extension. -/
def seqLeft
    (r₁ r₂ : NormResult D Γ) :
    Framed D (flagExt Γ (r₁.ids ++ r₂.ids)) :=
  r₁.loop.retagOn
    (flagExt_mono Γ (subsetAppendLeft r₁.ids r₂.ids))

/- The right sub-result read over the same extension. -/
def seqRight
    (r₁ r₂ : NormResult D Γ) :
    Framed D (flagExt Γ (r₁.ids ++ r₂.ids)) :=
  r₂.loop.retagOn
    (flagExt_mono Γ (subsetAppendRight r₁.ids r₂.ids))

/-
  The sequence clause, in the note's priority: loop-free
  side first, product second, general merge last.
-/
def seqResult
    (s : FlagSupply Γ)
    (k : Nat)
    (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ) :
    NormResult D Γ :=
  if LoopFree C₁ then
    ⟨r₁.ids ++ r₂.ids,
      mergeIntoPrefix (seqLeft r₁ r₂)
        (seqRight r₁ r₂)⟩
  else if LoopFree C₂ then
    ⟨r₁.ids ++ r₂.ids,
      mergeIntoSuffix (seqLeft r₁ r₂)
        (seqRight r₁ r₂)⟩
  else if independentCheck C₁ C₂ then
    ⟨r₁.ids ++ r₂.ids,
      mergeProduct (seqLeft r₁ r₂) (seqRight r₁ r₂)⟩
  else
    ⟨r₁.ids ++ r₂.ids ++
        [flagAt s (k + (r₁.ids ++ r₂.ids).length),
          flagAt s (k + (r₁.ids ++ r₂.ids).length + 1)],
      mergeGeneral
        (flagExt_mono Γ (subsetAppendLeft _ _))
        (drawnFlag s _
          (k + (r₁.ids ++ r₂.ids).length) (by simp))
        (drawnFlag s _
          (k + (r₁.ids ++ r₂.ids).length + 1) (by simp))
        (seqLeft r₁ r₂) (seqRight r₁ r₂)⟩

/- The conditional clause: always one drawn flag. -/
def iteResult
    (s : FlagSupply Γ)
    (k : Nat)
    (G : Guard D Γ)
    (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ) :
    NormResult D Γ :=
  ⟨r₁.ids ++ r₂.ids ++
      [flagAt s (k + (r₁.ids ++ r₂.ids).length)],
    hoistIte (flagExt_mono Γ (subsetAppendLeft _ _))
      (drawnFlag s _
        (k + (r₁.ids ++ r₂.ids).length) (by simp))
      (G.onExtension
        (flagExt_extensionOf Γ (r₁.ids ++ r₂.ids)))
      (seqLeft r₁ r₂) (seqRight r₁ r₂)
      (decide (LoopFree C₁)) (decide (LoopFree C₂))⟩

/- The loop clause with a loop-free source body. -/
def loopFreeResult
    (G : Guard D Γ)
    (C₀ : Cmd D Γ) :
    NormResult D Γ where
  ids := []
  loop :=
    (flattenLoopFree G C₀).retagOn
      (flagExt_extensionOf Γ [])

/- The loop clause with a nested loop: one drawn flag. -/
def loopResult
    (s : FlagSupply Γ)
    (k : Nat)
    (G : Guard D Γ)
    (r₀ : NormResult D Γ) :
    NormResult D Γ :=
  ⟨r₀.ids ++ [flagAt s (k + r₀.ids.length)],
    flattenGeneral (flagExt_mono Γ (subsetAppendLeft _ _))
      (drawnFlag s _ (k + r₀.ids.length) (by simp))
      (G.onExtension (flagExt_extensionOf Γ r₀.ids))
      r₀.loop⟩

/-
  The recursion. The loop-free clause takes priority over
  the three constructor clauses, whatever the constructor;
  the counter is threaded left to right by the budget, so
  the identifiers of two sibling calls are disjoint.
-/
def normalizeAux
    (s : FlagSupply Γ)
    (k : Nat) :
    Cmd D Γ → NormResult D Γ
| .skip => baseResult .skip
| .assign X e => baseResult (.assign X e)
| .seq C₁ C₂ =>
    if LoopFree (.seq C₁ C₂) then
      baseResult (.seq C₁ C₂)
    else
      seqResult s k C₁ C₂ (normalizeAux s k C₁)
        (normalizeAux s (k + flagBudget C₁) C₂)
| .ite G C₁ C₂ =>
    if LoopFree (.ite G C₁ C₂) then
      baseResult (.ite G C₁ C₂)
    else
      iteResult s k G C₁ C₂ (normalizeAux s k C₁)
        (normalizeAux s (k + flagBudget C₁) C₂)
| .«while» G C₀ =>
    if idemCheck G C₀ then
      normalizeAux s k C₀
    else if LoopFree C₀ then
      loopFreeResult G C₀
    else
      loopResult s k G (normalizeAux s k C₀)

/-
  The final clean, applied to the recursion's result: the
  repository's `Cmd.clean` on the prefix, the body and the
  suffix. It drops the sequencing `skip`s the loop-free
  sub-results contributed, and it keeps the `skip`s that are
  branches of a conditional, which carry the content of the
  product's stutter and of a hoist's empty close. The drawn
  identifiers are untouched.
-/
def NormResult.clean (r : NormResult D Γ) : NormResult D Γ
    where
  ids := r.ids
  loop := r.loop.clean

@[simp] theorem NormResult.clean_ids
    (r : NormResult D Γ) :
    r.clean.ids = r.ids :=
  rfl

@[simp] theorem NormResult.clean_loop
    (r : NormResult D Γ) :
    r.clean.loop = r.loop.clean :=
  rfl

/-
  The normalizer, from an empty flag supply, ending with the
  final clean.
-/
def normalize (C : Cmd D Γ) : NormResult D Γ :=
  (normalizeAux (FlagSupply.initial Γ) 0 C).clean

/- The uncleaned result the recursion returns. -/
def normalizeRaw (C : Cmd D Γ) : NormResult D Γ :=
  normalizeAux (FlagSupply.initial Γ) 0 C

@[simp] theorem normalize_eq_clean_normalizeRaw
    (C : Cmd D Γ) :
    normalize C = (normalizeRaw C).clean :=
  rfl

/-
  The first flag identifier the recursion leaves free. The
  supply is a counter, so this is plain arithmetic on the
  seed and the budget: the preamble push of the note's
  Section 4.1 draws exactly this identifier, at the top and
  last.
-/
def normalizeNext (C : Cmd D Γ) : Nat :=
  flagSeed Γ + flagBudget C

/- The schema the normalizer's output lives over. -/
def normalizeSchema
    (Γ : UnnamedSchema ProgramNames)
    (C : Cmd D Γ) :
    UnnamedSchema ProgramNames :=
  flagExt Γ (normalize C).ids

end Preprocess

end Whiel

------------------------------------------------------------
-- The Identifiers The Recursion Draws
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}
variable (s : FlagSupply Γ)

theorem flagAt_add
    (k m : Nat) :
    flagAt s (k + m) = flagAt s k + m := by
  simp only [flagAt, Nat.add_assoc]

theorem flagIds_append_one
    (a m : Nat) :
    flagIds a m ++ [a + m] = flagIds a (m + 1) := by
  rw [← flagIds_one (a + m), flagIds_append]

theorem flagIds_append_two
    (a m : Nat) :
    flagIds a m ++ [a + m, a + m + 1] =
      flagIds a (m + 2) := by
  rw [← flagIds_two (a + m), flagIds_append]

@[simp] theorem baseResult_ids
    (C : Cmd D Γ) :
    (baseResult C).ids = [] :=
  rfl

@[simp] theorem loopFreeResult_ids
    (G : Guard D Γ)
    (C₀ : Cmd D Γ) :
    (loopFreeResult G C₀).ids = [] :=
  rfl

theorem seqResult_ids_first
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (h : LoopFree C₁) :
    (seqResult s k C₁ C₂ r₁ r₂).ids =
      r₁.ids ++ r₂.ids := by
  simp only [seqResult, if_pos h]

theorem seqResult_ids_second
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (h₁ : ¬ LoopFree C₁)
    (h₂ : LoopFree C₂) :
    (seqResult s k C₁ C₂ r₁ r₂).ids =
      r₁.ids ++ r₂.ids := by
  simp only [seqResult, if_neg h₁, if_pos h₂]

theorem seqResult_ids_product
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (h₁ : ¬ LoopFree C₁)
    (h₂ : ¬ LoopFree C₂)
    (h₃ : independentCheck C₁ C₂ = true) :
    (seqResult s k C₁ C₂ r₁ r₂).ids =
      r₁.ids ++ r₂.ids := by
  simp only [seqResult, if_neg h₁, if_neg h₂, if_pos h₃]

theorem seqResult_ids_general
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (h₁ : ¬ LoopFree C₁)
    (h₂ : ¬ LoopFree C₂)
    (h₃ : ¬ (independentCheck C₁ C₂ = true)) :
    (seqResult s k C₁ C₂ r₁ r₂).ids =
      r₁.ids ++ r₂.ids ++
        [flagAt s (k + (r₁.ids ++ r₂.ids).length),
          flagAt s
            (k + (r₁.ids ++ r₂.ids).length + 1)] := by
  simp only [seqResult, if_neg h₁, if_neg h₂, if_neg h₃]

@[simp] theorem iteResult_ids
    (k : Nat) (G : Guard D Γ) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ) :
    (iteResult s k G C₁ C₂ r₁ r₂).ids =
      r₁.ids ++ r₂.ids ++
        [flagAt s (k + (r₁.ids ++ r₂.ids).length)] :=
  rfl

@[simp] theorem loopResult_ids
    (k : Nat) (G : Guard D Γ)
    (r₀ : NormResult D Γ) :
    (loopResult s k G r₀).ids =
      r₀.ids ++ [flagAt s (k + r₀.ids.length)] :=
  rfl

/-
  The identifier-range statement: the recursion draws
  exactly the budget's worth of consecutive identifiers,
  starting at the offset it was handed.
-/
theorem normalizeAux_ids s
    (k : Nat)
    (C : Cmd D Γ) :
    (normalizeAux s k C).ids =
      flagIds (flagAt s k) (flagBudget C) := by
  induction C generalizing k with
  | skip => rfl
  | assign X e => rfl
  | seq C₁ C₂ ih₁ ih₂ =>
      by_cases hFree : LoopFree (Cmd.seq C₁ C₂)
      · simp only [normalizeAux, if_pos hFree,
          baseResult_ids,
          flagBudget_eq_zero_of_loopFree hFree,
          flagIds_zero]
      · have hPair :
            (normalizeAux s k C₁).ids ++
                (normalizeAux s (k + flagBudget C₁)
                  C₂).ids =
              flagIds (flagAt s k)
                (flagBudget C₁ + flagBudget C₂) := by
          rw [ih₁ k, ih₂ (k + flagBudget C₁), flagAt_add,
            flagIds_append]
        simp only [normalizeAux, if_neg hFree]
        by_cases h₁ : LoopFree C₁
        · rw [seqResult_ids_first s k C₁ C₂ _ _ h₁, hPair]
          simp only [flagBudget, if_pos h₁, Nat.add_zero]
        · by_cases h₂ : LoopFree C₂
          · rw [seqResult_ids_second s k C₁ C₂ _ _ h₁ h₂,
              hPair]
            simp only [flagBudget, if_neg h₁, if_pos h₂,
              Nat.add_zero]
          · by_cases h₃ : independentCheck C₁ C₂ = true
            · rw [seqResult_ids_product s k C₁ C₂ _ _
                  h₁ h₂ h₃, hPair]
              simp only [flagBudget, if_neg h₁, if_neg h₂,
                if_pos h₃, Nat.add_zero]
            · rw [seqResult_ids_general s k C₁ C₂ _ _
                  h₁ h₂ h₃, hPair, length_flagIds,
                flagAt_add s
                  (k + (flagBudget C₁ + flagBudget C₂)) 1,
                flagAt_add s k
                  (flagBudget C₁ + flagBudget C₂),
                flagIds_append_two]
              simp only [flagBudget, if_neg h₁, if_neg h₂,
                if_neg h₃]
  | ite G C₁ C₂ ih₁ ih₂ =>
      by_cases hFree : LoopFree (Cmd.ite G C₁ C₂)
      · simp only [normalizeAux, if_pos hFree,
          baseResult_ids,
          flagBudget_eq_zero_of_loopFree hFree,
          flagIds_zero]
      · have hPair :
            (normalizeAux s k C₁).ids ++
                (normalizeAux s (k + flagBudget C₁)
                  C₂).ids =
              flagIds (flagAt s k)
                (flagBudget C₁ + flagBudget C₂) := by
          rw [ih₁ k, ih₂ (k + flagBudget C₁), flagAt_add,
            flagIds_append]
        have hDrawn :
            (if LoopFree C₁ then
                (if LoopFree C₂ then 0 else 1)
              else 1) = 1 := by
          by_cases h₁ : LoopFree C₁
          · by_cases h₂ : LoopFree C₂
            · exact absurd
                ((loopFree_ite_iff G C₁ C₂).mpr
                  ⟨h₁, h₂⟩)
                hFree
            · simp only [if_pos h₁, if_neg h₂]
          · simp only [if_neg h₁]
        simp only [normalizeAux, if_neg hFree,
          iteResult_ids]
        rw [hPair, length_flagIds,
          flagAt_add s k
            (flagBudget C₁ + flagBudget C₂),
          flagIds_append_one]
        simp only [flagBudget, hDrawn]
  | «while» G C₀ ih =>
      by_cases hIdem : idemCheck G C₀ = true
      · simp only [normalizeAux, if_pos hIdem]
        rw [ih k]
        simp only [flagBudget, if_pos hIdem, Nat.add_zero]
      · by_cases hLF : LoopFree C₀
        · simp only [normalizeAux, if_neg hIdem,
            loopFreeResult_ids, flagBudget,
            if_pos hLF, Nat.add_zero,
            flagBudget_eq_zero_of_loopFree hLF,
            flagIds_zero]
        · simp only [normalizeAux, if_neg hIdem,
            if_neg hLF, loopResult_ids]
          rw [ih k, length_flagIds, flagAt_add s k,
            flagIds_append_one]
          simp only [flagBudget, if_neg hIdem, if_neg hLF]

/- The normalizer draws exactly the budget's identifiers. -/
theorem normalize_ids
    (C : Cmd D Γ) :
    (normalize C).ids =
      flagIds (flagSeed Γ) (flagBudget C) :=
  normalizeAux_ids (FlagSupply.initial Γ) 0 C

/- The push identifier is fresh for the input schema. -/
theorem flagName_normalizeNext_not_mem
    (C : Cmd D Γ) :
    flagName (normalizeNext C) ∉ Γ.syms :=
  flagName_not_mem_of_flagSeed_le (Nat.le_add_right _ _)

/- The push identifier is not one the recursion drew. -/
theorem normalizeNext_not_mem_ids
    (C : Cmd D Γ) :
    normalizeNext C ∉ (normalize C).ids := by
  rw [normalize_ids, mem_flagIds_iff]
  simp only [normalizeNext]
  omega

/- The number of identifiers drawn is the budget. -/
theorem normalize_ids_length
    (C : Cmd D Γ) :
    (normalize C).ids.length = flagBudget C := by
  rw [normalize_ids, length_flagIds]

end Preprocess

end Whiel


------------------------------------------------------------
-- The Clauses Of The Recursion
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}
variable (s : FlagSupply Γ)

/-
  The clauses, as equations between results. Every proof
  below rewrites with these rather than unfolding under the
  dependent second component.
-/
theorem seqResult_eq_intoPrefix
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (h : LoopFree C₁) :
    seqResult s k C₁ C₂ r₁ r₂ =
      ⟨r₁.ids ++ r₂.ids,
        mergeIntoPrefix (seqLeft r₁ r₂)
          (seqRight r₁ r₂)⟩ := by
  simp only [seqResult, if_pos h]

theorem seqResult_eq_intoSuffix
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (h₁ : ¬ LoopFree C₁)
    (h₂ : LoopFree C₂) :
    seqResult s k C₁ C₂ r₁ r₂ =
      ⟨r₁.ids ++ r₂.ids,
        mergeIntoSuffix (seqLeft r₁ r₂)
          (seqRight r₁ r₂)⟩ := by
  simp only [seqResult, if_neg h₁, if_pos h₂]

theorem seqResult_eq_product
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (h₁ : ¬ LoopFree C₁)
    (h₂ : ¬ LoopFree C₂)
    (h₃ : independentCheck C₁ C₂ = true) :
    seqResult s k C₁ C₂ r₁ r₂ =
      ⟨r₁.ids ++ r₂.ids,
        mergeProduct (seqLeft r₁ r₂)
          (seqRight r₁ r₂)⟩ := by
  simp only [seqResult, if_neg h₁, if_neg h₂, if_pos h₃]

theorem seqResult_eq_general
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (h₁ : ¬ LoopFree C₁)
    (h₂ : ¬ LoopFree C₂)
    (h₃ : ¬ (independentCheck C₁ C₂ = true)) :
    seqResult s k C₁ C₂ r₁ r₂ =
      ⟨r₁.ids ++ r₂.ids ++
          [flagAt s (k + (r₁.ids ++ r₂.ids).length),
            flagAt s
              (k + (r₁.ids ++ r₂.ids).length + 1)],
        mergeGeneral
          (flagExt_mono Γ (subsetAppendLeft _ _))
          (drawnFlag s _
            (k + (r₁.ids ++ r₂.ids).length) (by simp))
          (drawnFlag s _
            (k + (r₁.ids ++ r₂.ids).length + 1)
            (by simp))
          (seqLeft r₁ r₂) (seqRight r₁ r₂)⟩ := by
  simp only [seqResult, if_neg h₁, if_neg h₂, if_neg h₃]

theorem normalizeAux_eq_base_seq s
    (k : Nat) {C₁ C₂ : Cmd D Γ}
    (h : LoopFree (Cmd.seq C₁ C₂)) :
    normalizeAux s k (Cmd.seq C₁ C₂) =
      baseResult (Cmd.seq C₁ C₂) := by
  simp only [normalizeAux, if_pos h]

theorem normalizeAux_eq_seq s
    (k : Nat) {C₁ C₂ : Cmd D Γ}
    (h : ¬ LoopFree (Cmd.seq C₁ C₂)) :
    normalizeAux s k (Cmd.seq C₁ C₂) =
      seqResult s k C₁ C₂ (normalizeAux s k C₁)
        (normalizeAux s (k + flagBudget C₁) C₂) := by
  simp only [normalizeAux, if_neg h]

theorem normalizeAux_eq_base_ite s
    (k : Nat) {G : Guard D Γ} {C₁ C₂ : Cmd D Γ}
    (h : LoopFree (Cmd.ite G C₁ C₂)) :
    normalizeAux s k (Cmd.ite G C₁ C₂) =
      baseResult (Cmd.ite G C₁ C₂) := by
  simp only [normalizeAux, if_pos h]

theorem normalizeAux_eq_ite s
    (k : Nat) {G : Guard D Γ} {C₁ C₂ : Cmd D Γ}
    (h : ¬ LoopFree (Cmd.ite G C₁ C₂)) :
    normalizeAux s k (Cmd.ite G C₁ C₂) =
      iteResult s k G C₁ C₂ (normalizeAux s k C₁)
        (normalizeAux s (k + flagBudget C₁) C₂) := by
  simp only [normalizeAux, if_neg h]

theorem normalizeAux_eq_idem s
    (k : Nat) {G : Guard D Γ} {C₀ : Cmd D Γ}
    (h : idemCheck G C₀ = true) :
    normalizeAux s k (Cmd.«while» G C₀) =
      normalizeAux s k C₀ := by
  simp only [normalizeAux, if_pos h]

theorem normalizeAux_eq_loopFreeBody s
    (k : Nat) {G : Guard D Γ} {C₀ : Cmd D Γ}
    (hIdem : ¬ (idemCheck G C₀ = true))
    (hFree : LoopFree C₀) :
    normalizeAux s k (Cmd.«while» G C₀) =
      loopFreeResult G C₀ := by
  simp only [normalizeAux, if_neg hIdem, if_pos hFree]

theorem normalizeAux_eq_flatten s
    (k : Nat) {G : Guard D Γ} {C₀ : Cmd D Γ}
    (hIdem : ¬ (idemCheck G C₀ = true))
    (hFree : ¬ LoopFree C₀) :
    normalizeAux s k (Cmd.«while» G C₀) =
      loopResult s k G (normalizeAux s k C₀) := by
  simp only [normalizeAux, if_neg hIdem, if_neg hFree]

end Preprocess

end Whiel

------------------------------------------------------------
-- The Shape Of The Output
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- Retagging keeps the loop-free components loop-free. -/
theorem loopFreeParts_retagOn
    (hExt : Ω.extensionOf Δ)
    {L : Framed D Δ}
    (hParts : L.LoopFreeParts) :
    (L.retagOn hExt).LoopFreeParts :=
  ⟨loopFree_of_retag hExt hParts.1,
    loopFree_of_retag hExt hParts.2.1,
    loopFree_of_retag hExt hParts.2.2⟩

end Preprocess

end Whiel

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}
variable (s : FlagSupply Γ)

theorem baseResult_loopFreeParts
    {C : Cmd D Γ}
    (hFree : LoopFree C) :
    (baseResult C).loop.LoopFreeParts :=
  loopFreeParts_retagOn _
    ((Framed.loopFreeParts_base_iff C).mpr hFree)

theorem seqLeft_loopFreeParts
    {r₁ r₂ : NormResult D Γ}
    (hParts : r₁.loop.LoopFreeParts) :
    (seqLeft r₁ r₂).LoopFreeParts :=
  loopFreeParts_retagOn _ hParts

theorem seqRight_loopFreeParts
    {r₁ r₂ : NormResult D Γ}
    (hParts : r₂.loop.LoopFreeParts) :
    (seqRight r₁ r₂).LoopFreeParts :=
  loopFreeParts_retagOn _ hParts

theorem seqResult_loopFreeParts
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    {r₁ r₂ : NormResult D Γ}
    (hOne : r₁.loop.LoopFreeParts)
    (hTwo : r₂.loop.LoopFreeParts) :
    (seqResult s k C₁ C₂ r₁ r₂).loop.LoopFreeParts := by
  have hL := seqLeft_loopFreeParts (r₂ := r₂) hOne
  have hR := seqRight_loopFreeParts (r₁ := r₁) hTwo
  by_cases h₁ : LoopFree C₁
  · rw [seqResult_eq_intoPrefix s k C₁ C₂ r₁ r₂ h₁]
    exact mergeIntoPrefix_loopFreeParts hL hR
  · by_cases h₂ : LoopFree C₂
    · rw [seqResult_eq_intoSuffix s k C₁ C₂ r₁ r₂ h₁
          h₂]
      exact mergeIntoSuffix_loopFreeParts hL hR
    · by_cases h₃ : independentCheck C₁ C₂ = true
      · rw [seqResult_eq_product s k C₁ C₂ r₁ r₂ h₁
            h₂ h₃]
        exact mergeProduct_loopFreeParts hL hR
      · rw [seqResult_eq_general s k C₁ C₂ r₁ r₂ h₁
            h₂ h₃]
        exact mergeGeneral_loopFreeParts _ _ _ hL hR

theorem iteResult_loopFreeParts
    (k : Nat) (G : Guard D Γ) (C₁ C₂ : Cmd D Γ)
    {r₁ r₂ : NormResult D Γ}
    (hOne : r₁.loop.LoopFreeParts)
    (hTwo : r₂.loop.LoopFreeParts) :
    (iteResult s k G C₁ C₂ r₁ r₂).loop.LoopFreeParts :=
  hoistIte_loopFreeParts _ _ _ _ _ _ _
    (seqLeft_loopFreeParts (r₂ := r₂) hOne)
    (seqRight_loopFreeParts (r₁ := r₁) hTwo)

theorem loopFreeResult_loopFreeParts
    (G : Guard D Γ)
    {C₀ : Cmd D Γ}
    (hFree : LoopFree C₀) :
    (loopFreeResult G C₀).loop.LoopFreeParts :=
  loopFreeParts_retagOn _
    (flattenLoopFree_loopFreeParts G hFree)

theorem loopResult_loopFreeParts
    (k : Nat) (G : Guard D Γ)
    {r₀ : NormResult D Γ}
    (hParts : r₀.loop.LoopFreeParts) :
    (loopResult s k G r₀).loop.LoopFreeParts :=
  flattenGeneral_loopFreeParts _ _ _ hParts

/-
  Proposition "Totality, shape, determinism". Totality and
  determinism are the totality and functionhood of the
  structural recursion; what needs proof is the shape, that
  the result is a framed loop with loop-free parts.
-/
theorem normalizeAux_loopFreeParts s
    (k : Nat)
    (C : Cmd D Γ) :
    (normalizeAux s k C).loop.LoopFreeParts := by
  induction C generalizing k with
  | skip => exact baseResult_loopFreeParts rfl
  | assign X e => exact baseResult_loopFreeParts rfl
  | seq C₁ C₂ ih₁ ih₂ =>
      by_cases hFree : LoopFree (Cmd.seq C₁ C₂)
      · rw [normalizeAux_eq_base_seq s k hFree]
        exact baseResult_loopFreeParts hFree
      · rw [normalizeAux_eq_seq s k hFree]
        exact seqResult_loopFreeParts s k C₁ C₂ (ih₁ k)
          (ih₂ (k + flagBudget C₁))
  | ite G C₁ C₂ ih₁ ih₂ =>
      by_cases hFree : LoopFree (Cmd.ite G C₁ C₂)
      · rw [normalizeAux_eq_base_ite s k hFree]
        exact baseResult_loopFreeParts hFree
      · rw [normalizeAux_eq_ite s k hFree]
        exact iteResult_loopFreeParts s k G C₁ C₂ (ih₁ k)
          (ih₂ (k + flagBudget C₁))
  | «while» G C₀ ih =>
      by_cases hIdem : idemCheck G C₀ = true
      · rw [normalizeAux_eq_idem s k hIdem]
        exact ih k
      · by_cases hLF : LoopFree C₀
        · rw [normalizeAux_eq_loopFreeBody s k hIdem hLF]
          exact loopFreeResult_loopFreeParts G hLF
        · rw [normalizeAux_eq_flatten s k hIdem hLF]
          exact loopResult_loopFreeParts s k G (ih k)

/- The unfolding of the output has exactly one loop. -/
theorem loops_normalizeAux_unfold
    (k : Nat)
    (C : Cmd D Γ) :
    loops (normalizeAux s k C).loop.unfold = 1 :=
  Framed.loops_unfold (normalizeAux_loopFreeParts s k C)

/-
  The final clean keeps the loop-free components loop-free,
  so the shape clause of Proposition "Totality, shape,
  determinism" survives it.
-/
theorem normalize_loopFreeParts
    (C : Cmd D Γ) :
    (normalize C).loop.LoopFreeParts :=
  Framed.loopFreeParts_clean
    (normalizeAux_loopFreeParts (FlagSupply.initial Γ) 0 C)

theorem loops_normalize_unfold
    (C : Cmd D Γ) :
    loops (normalize C).loop.unfold = 1 :=
  Framed.loops_unfold (normalize_loopFreeParts C)

end Preprocess

end Whiel

------------------------------------------------------------
-- Footprints Of The Operations
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

@[simp] theorem symbols_topExpr
    (f : FlagSym Ω) :
    (f.topExpr (D := D)).symbols = (∅ : Finset A) :=
  rfl

@[simp] theorem symbols_emptyExpr
    (f : FlagSym Ω) :
    (f.emptyExpr (D := D)).symbols = (∅ : Finset A) :=
  rfl

@[simp] theorem symbols_raise
    (f : FlagSym Ω) :
    (f.raise (D := D)).symbols = {f.sym.1} := by
  simp [FlagSym.raise, Cmd.symbols]

@[simp] theorem symbols_lower
    (f : FlagSym Ω) :
    (f.lower (D := D)).symbols = {f.sym.1} := by
  simp [FlagSym.lower, Cmd.symbols]

@[simp] theorem symbols_test
    (f : FlagSym Ω) :
    (f.test (D := D)).symbols = {f.sym.1} := by
  simp [FlagSym.test, FlagSym.topExpr, Guard.symbols,
    RAExpr.symbols, RAExpr.rel, RAExpr.castArity,
    RAExpr.top, RawRAExpr.symbols]

@[simp] theorem symbols_unfold_retagOn
    (hExt : Ω.extensionOf Δ)
    (L : Framed D Δ) :
    (L.retagOn hExt).unfold.symbols = L.unfold.symbols := by
  rw [Framed.unfold_retagOn, symbols_retag]

@[simp] theorem assignedSymbols_unfold_retagOn
    (hExt : Ω.extensionOf Δ)
    (L : Framed D Δ) :
    (L.retagOn hExt).unfold.assignedSymbols =
      L.unfold.assignedSymbols := by
  rw [Framed.unfold_retagOn, assignedSymbols_retag]

@[simp] theorem symbols_unfold_base
    (C : Cmd D Δ) :
    (Framed.base C).unfold.symbols = C.symbols := by
  simp [Framed.base, Framed.unfold, Cmd.symbols,
    Guard.symbols]

@[simp] theorem assignedSymbols_unfold_base
    (C : Cmd D Δ) :
    (Framed.base C).unfold.assignedSymbols =
      C.assignedSymbols := by
  simp [Framed.base, Framed.unfold, Cmd.assignedSymbols]

theorem mergeIntoPrefix_symbols_subset
    (L₁ L₂ : Framed D Δ) :
    (mergeIntoPrefix L₁ L₂).unfold.symbols ⊆
      L₁.unfold.symbols ∪ L₂.unfold.symbols := by
  intro X hX
  simp only [mem_unfold_symbols_iff, mergeIntoPrefix,
    Cmd.symbols, Finset.mem_union] at hX ⊢
  tauto

theorem mergeIntoPrefix_assignedSymbols_subset
    (L₁ L₂ : Framed D Δ) :
    (mergeIntoPrefix L₁ L₂).unfold.assignedSymbols ⊆
      L₁.unfold.assignedSymbols ∪
        L₂.unfold.assignedSymbols := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff,
    mergeIntoPrefix, Cmd.assignedSymbols,
    Finset.mem_union] at hX ⊢
  tauto

theorem mergeIntoSuffix_symbols_subset
    (L₁ L₂ : Framed D Δ) :
    (mergeIntoSuffix L₁ L₂).unfold.symbols ⊆
      L₁.unfold.symbols ∪ L₂.unfold.symbols := by
  intro X hX
  simp only [mem_unfold_symbols_iff, mergeIntoSuffix,
    Cmd.symbols, Finset.mem_union] at hX ⊢
  tauto

theorem mergeIntoSuffix_assignedSymbols_subset
    (L₁ L₂ : Framed D Δ) :
    (mergeIntoSuffix L₁ L₂).unfold.assignedSymbols ⊆
      L₁.unfold.assignedSymbols ∪
        L₂.unfold.assignedSymbols := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff,
    mergeIntoSuffix, Cmd.assignedSymbols,
    Finset.mem_union] at hX ⊢
  tauto

theorem mergeProduct_symbols_subset
    (L₁ L₂ : Framed D Δ) :
    (mergeProduct L₁ L₂).unfold.symbols ⊆
      L₁.unfold.symbols ∪ L₂.unfold.symbols := by
  intro X hX
  simp only [mem_unfold_symbols_iff, mergeProduct,
    productBody, Cmd.symbols, Guard.symbols,
    Finset.mem_union] at hX ⊢
  tauto

theorem mergeProduct_assignedSymbols_subset
    (L₁ L₂ : Framed D Δ) :
    (mergeProduct L₁ L₂).unfold.assignedSymbols ⊆
      L₁.unfold.assignedSymbols ∪
        L₂.unfold.assignedSymbols := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff, mergeProduct,
    productBody, Cmd.assignedSymbols,
    Finset.mem_union] at hX ⊢
  tauto

theorem mergeGeneral_symbols_subset
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    (mergeGeneral hExt f₁ f₂ L₁ L₂).unfold.symbols ⊆
      L₁.unfold.symbols ∪ L₂.unfold.symbols ∪
        {f₁.sym.1, f₂.sym.1} := by
  intro X hX
  simp only [mem_unfold_symbols_iff, mergeGeneral,
    mergeGeneralBody, mergeSwitch, Cmd.symbols,
    Guard.symbols, symbols_retag, symbols_raise,
    symbols_lower, symbols_test,
    Guard.symbols_onExtension, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hX ⊢
  tauto

theorem mergeGeneral_assignedSymbols_subset
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    (mergeGeneral hExt f₁ f₂
        L₁ L₂).unfold.assignedSymbols ⊆
      L₁.unfold.assignedSymbols ∪
          L₂.unfold.assignedSymbols ∪
        {f₁.sym.1, f₂.sym.1} := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff, mergeGeneral,
    mergeGeneralBody, mergeSwitch, Cmd.assignedSymbols,
    assignedSymbols_retag, FlagSym.assignedSymbols_raise,
    FlagSym.assignedSymbols_lower, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hX ⊢
  tauto

theorem hoistIte_symbols_subset
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (b c : Bool) :
    (hoistIte hExt f G L₁ L₂ b c).unfold.symbols ⊆
      L₁.unfold.symbols ∪ L₂.unfold.symbols ∪
        (G.symbols ∪ {f.sym.1}) := by
  intro X hX
  cases b <;> cases c <;>
    simp only [hoistIte, mem_unfold_symbols_iff,
      hoistGeneral, hoistThenLoop, hoistElseLoop,
      hoistFlagFree, hoistOf, hoistInit, hoistBody,
      hoistClose, hoistGuard, Framed.retagOn, Framed.base,
      Cmd.symbols, Guard.symbols, symbols_retag,
      symbols_raise, symbols_lower, symbols_test,
      Guard.symbols_onExtension, Finset.mem_union,
      Finset.mem_singleton, Bool.false_eq_true,
      if_true, if_false] at hX ⊢ <;>
    tauto

theorem hoistIte_assignedSymbols_subset
    (hExt : Ω.extensionOf Δ)
    (f : FlagSym Ω)
    (G : Guard D Δ)
    (L₁ L₂ : Framed D Δ)
    (b c : Bool) :
    (hoistIte hExt f G L₁ L₂ b
        c).unfold.assignedSymbols ⊆
      L₁.unfold.assignedSymbols ∪
          L₂.unfold.assignedSymbols ∪
        {f.sym.1} := by
  intro X hX
  cases b <;> cases c <;>
    simp only [hoistIte, mem_unfold_assignedSymbols_iff,
      hoistGeneral, hoistThenLoop, hoistElseLoop,
      hoistFlagFree, hoistOf, hoistInit, hoistBody,
      hoistClose, Framed.retagOn, Framed.base,
      Cmd.assignedSymbols, assignedSymbols_retag,
      FlagSym.assignedSymbols_raise,
      FlagSym.assignedSymbols_lower, Finset.mem_union,
      Finset.mem_singleton, Bool.false_eq_true,
      if_true, if_false] at hX ⊢ <;>
    tauto

theorem flattenGeneral_symbols_subset
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (L₀ : Framed D Δ) :
    (flattenGeneral hExt i G L₀).unfold.symbols ⊆
      L₀.unfold.symbols ∪ (G.symbols ∪ {i.sym.1}) := by
  intro X hX
  simp only [mem_unfold_symbols_iff, flattenGeneral,
    flattenGuard, flattenBody, Cmd.symbols, Guard.symbols,
    symbols_retag, symbols_raise, symbols_lower,
    symbols_test, Guard.symbols_onExtension,
    Finset.mem_union, Finset.mem_singleton] at hX ⊢
  tauto

theorem flattenGeneral_assignedSymbols_subset
    (hExt : Ω.extensionOf Δ)
    (i : FlagSym Ω)
    (G : Guard D Δ)
    (L₀ : Framed D Δ) :
    (flattenGeneral hExt i G L₀).unfold.assignedSymbols ⊆
      L₀.unfold.assignedSymbols ∪ {i.sym.1} := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff, flattenGeneral,
    flattenBody, Cmd.assignedSymbols, assignedSymbols_retag,
    FlagSym.assignedSymbols_raise,
    FlagSym.assignedSymbols_lower, Finset.mem_union,
    Finset.mem_singleton] at hX ⊢
  tauto

theorem flattenLoopFree_symbols_subset
    (G : Guard D Δ)
    (C₀ : Cmd D Δ) :
    (flattenLoopFree G C₀).unfold.symbols ⊆
      C₀.symbols ∪ G.symbols := by
  intro X hX
  simp only [mem_unfold_symbols_iff, flattenLoopFree,
    Cmd.symbols, Finset.mem_union] at hX ⊢
  tauto

theorem flattenLoopFree_assignedSymbols_subset
    (G : Guard D Δ)
    (C₀ : Cmd D Δ) :
    (flattenLoopFree G C₀).unfold.assignedSymbols ⊆
      C₀.assignedSymbols := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff,
    flattenLoopFree,
    Cmd.assignedSymbols] at hX ⊢
  tauto

end Preprocess

end Whiel

------------------------------------------------------------
-- The Footprint Lemma
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A : Type}
variable [RelationNames A]

/- Assembling a footprint from two sub-footprints. -/
theorem footprint_combine
    {S S₁ S₂ E B B₁ B₂ F F₁ F₂ : Finset A}
    (hS : S ⊆ S₁ ∪ S₂ ∪ E)
    (h₁ : S₁ ⊆ B₁ ∪ F₁)
    (h₂ : S₂ ⊆ B₂ ∪ F₂)
    (hB₁ : B₁ ⊆ B)
    (hB₂ : B₂ ⊆ B)
    (hF₁ : F₁ ⊆ F)
    (hF₂ : F₂ ⊆ F)
    (hE : E ⊆ B ∪ F) :
    S ⊆ B ∪ F := by
  intro X hX
  rcases Finset.mem_union.mp (hS hX) with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp (h₁ h) with h | h
      · exact Finset.mem_union_left _ (hB₁ h)
      · exact Finset.mem_union_right _ (hF₁ h)
    · rcases Finset.mem_union.mp (h₂ h) with h | h
      · exact Finset.mem_union_left _ (hB₂ h)
      · exact Finset.mem_union_right _ (hF₂ h)
  · exact hE h

/- The same with no extra symbols. -/
theorem footprint_combine₂
    {S S₁ S₂ B B₁ B₂ F F₁ F₂ : Finset A}
    (hS : S ⊆ S₁ ∪ S₂)
    (h₁ : S₁ ⊆ B₁ ∪ F₁)
    (h₂ : S₂ ⊆ B₂ ∪ F₂)
    (hB₁ : B₁ ⊆ B)
    (hB₂ : B₂ ⊆ B)
    (hF₁ : F₁ ⊆ F)
    (hF₂ : F₂ ⊆ F) :
    S ⊆ B ∪ F := by
  refine
    footprint_combine (E := ∅) ?_ h₁ h₂ hB₁ hB₂ hF₁
      hF₂ ?_
  · intro X hX
    exact Finset.mem_union_left _ (hS hX)
  · intro X hX
    exact absurd hX (by simp)

/- Assembling a footprint from one sub-footprint. -/
theorem footprint_combine_one
    {S S₀ E B B₀ F F₀ : Finset A}
    (hS : S ⊆ S₀ ∪ E)
    (h₀ : S₀ ⊆ B₀ ∪ F₀)
    (hB₀ : B₀ ⊆ B)
    (hF₀ : F₀ ⊆ F)
    (hE : E ⊆ B ∪ F) :
    S ⊆ B ∪ F := by
  intro X hX
  rcases Finset.mem_union.mp (hS hX) with h | h
  · rcases Finset.mem_union.mp (h₀ h) with h | h
    · exact Finset.mem_union_left _ (hB₀ h)
    · exact Finset.mem_union_right _ (hF₀ h)
  · exact hE h

end Preprocess

end Whiel

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}
variable (s : FlagSupply Γ)

@[simp] theorem seqLeft_symbols
    (r₁ r₂ : NormResult D Γ) :
    (seqLeft r₁ r₂).unfold.symbols =
      r₁.loop.unfold.symbols :=
  symbols_unfold_retagOn _ _

@[simp] theorem seqLeft_assignedSymbols
    (r₁ r₂ : NormResult D Γ) :
    (seqLeft r₁ r₂).unfold.assignedSymbols =
      r₁.loop.unfold.assignedSymbols :=
  assignedSymbols_unfold_retagOn _ _

@[simp] theorem seqRight_symbols
    (r₁ r₂ : NormResult D Γ) :
    (seqRight r₁ r₂).unfold.symbols =
      r₂.loop.unfold.symbols :=
  symbols_unfold_retagOn _ _

@[simp] theorem seqRight_assignedSymbols
    (r₁ r₂ : NormResult D Γ) :
    (seqRight r₁ r₂).unfold.assignedSymbols =
      r₂.loop.unfold.assignedSymbols :=
  assignedSymbols_unfold_retagOn _ _

@[simp] theorem baseResult_symbols
    (C : Cmd D Γ) :
    (baseResult C).loop.unfold.symbols = C.symbols := by
  simp only [baseResult, symbols_unfold_retagOn,
    symbols_unfold_base]

@[simp] theorem baseResult_assignedSymbols
    (C : Cmd D Γ) :
    (baseResult C).loop.unfold.assignedSymbols =
      C.assignedSymbols := by
  simp only [baseResult, assignedSymbols_unfold_retagOn,
    assignedSymbols_unfold_base]

@[simp] theorem loopFreeResult_symbols
    (G : Guard D Γ)
    (C₀ : Cmd D Γ) :
    (loopFreeResult G C₀).loop.unfold.symbols =
      (flattenLoopFree G C₀).unfold.symbols := by
  simp only [loopFreeResult, symbols_unfold_retagOn]

@[simp] theorem loopFreeResult_assignedSymbols
    (G : Guard D Γ)
    (C₀ : Cmd D Γ) :
    (loopFreeResult G C₀).loop.unfold.assignedSymbols =
      (flattenLoopFree G C₀).unfold.assignedSymbols := by
  simp only [loopFreeResult,
    assignedSymbols_unfold_retagOn]

/- A drawn flag's name is the identifier's flag name. -/
@[simp] theorem drawnFlag_sym_val
    (Φ : List Nat)
    (j : Nat)
    (hMem : flagAt s j ∈ Φ) :
    (drawnFlag s Φ j hMem).sym.1 =
      flagName (flagAt s j) :=
  rfl

theorem flagNames_mono
    {Φ₁ Φ₂ : List Nat}
    (hSub : Φ₁ ⊆ Φ₂) :
    flagNames Φ₁ ⊆ flagNames Φ₂ :=
  flagNames_subset hSub

/-
  Lemma "Footprint" for one sequence node: the merge adds
  only its own flags to the symbols and assigned sets of
  the two sub-results.
-/
theorem seqResult_footprint
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (hSymOne :
      r₁.loop.unfold.symbols ⊆
        C₁.symbols ∪ flagNames r₁.ids)
    (hAsgOne :
      r₁.loop.unfold.assignedSymbols ⊆
        C₁.assignedSymbols ∪ flagNames r₁.ids)
    (hSymTwo :
      r₂.loop.unfold.symbols ⊆
        C₂.symbols ∪ flagNames r₂.ids)
    (hAsgTwo :
      r₂.loop.unfold.assignedSymbols ⊆
        C₂.assignedSymbols ∪ flagNames r₂.ids) :
    (seqResult s k C₁ C₂ r₁ r₂).loop.unfold.symbols ⊆
        (Cmd.seq C₁ C₂).symbols ∪
          flagNames (seqResult s k C₁ C₂ r₁ r₂).ids ∧
      (seqResult s k C₁ C₂
            r₁ r₂).loop.unfold.assignedSymbols ⊆
        (Cmd.seq C₁ C₂).assignedSymbols ∪
          flagNames (seqResult s k C₁ C₂ r₁ r₂).ids := by
  have hBaseOne :
      C₁.symbols ⊆ (Cmd.seq C₁ C₂).symbols :=
    Finset.subset_union_left
  have hBaseTwo :
      C₂.symbols ⊆ (Cmd.seq C₁ C₂).symbols :=
    Finset.subset_union_right
  have hAsgBaseOne :
      C₁.assignedSymbols ⊆
        (Cmd.seq C₁ C₂).assignedSymbols :=
    Finset.subset_union_left
  have hAsgBaseTwo :
      C₂.assignedSymbols ⊆
        (Cmd.seq C₁ C₂).assignedSymbols :=
    Finset.subset_union_right
  have hSymL :
      (seqLeft r₁ r₂).unfold.symbols ⊆
        C₁.symbols ∪ flagNames r₁.ids := by
    rw [seqLeft_symbols]; exact hSymOne
  have hSymR :
      (seqRight r₁ r₂).unfold.symbols ⊆
        C₂.symbols ∪ flagNames r₂.ids := by
    rw [seqRight_symbols]; exact hSymTwo
  have hAsgL :
      (seqLeft r₁ r₂).unfold.assignedSymbols ⊆
        C₁.assignedSymbols ∪ flagNames r₁.ids := by
    rw [seqLeft_assignedSymbols]; exact hAsgOne
  have hAsgR :
      (seqRight r₁ r₂).unfold.assignedSymbols ⊆
        C₂.assignedSymbols ∪ flagNames r₂.ids := by
    rw [seqRight_assignedSymbols]; exact hAsgTwo
  by_cases h₁ : LoopFree C₁
  · rw [seqResult_eq_intoPrefix s k C₁ C₂ r₁ r₂ h₁]
    exact
      ⟨footprint_combine₂
        (mergeIntoPrefix_symbols_subset _ _) hSymL hSymR
        hBaseOne hBaseTwo
        (flagNames_mono (subsetAppendLeft _ _))
        (flagNames_mono (subsetAppendRight _ _)),
      footprint_combine₂
        (mergeIntoPrefix_assignedSymbols_subset _ _)
        hAsgL hAsgR hAsgBaseOne hAsgBaseTwo
        (flagNames_mono (subsetAppendLeft _ _))
        (flagNames_mono (subsetAppendRight _ _))⟩
  · by_cases h₂ : LoopFree C₂
    · rw [seqResult_eq_intoSuffix s k C₁ C₂ r₁ r₂ h₁
          h₂]
      exact
        ⟨footprint_combine₂
          (mergeIntoSuffix_symbols_subset _ _) hSymL hSymR
          hBaseOne hBaseTwo
          (flagNames_mono (subsetAppendLeft _ _))
          (flagNames_mono (subsetAppendRight _ _)),
        footprint_combine₂
          (mergeIntoSuffix_assignedSymbols_subset _ _)
          hAsgL hAsgR hAsgBaseOne hAsgBaseTwo
          (flagNames_mono (subsetAppendLeft _ _))
          (flagNames_mono (subsetAppendRight _ _))⟩
    · by_cases h₃ : independentCheck C₁ C₂ = true
      · rw [seqResult_eq_product s k C₁ C₂ r₁ r₂ h₁
            h₂ h₃]
        exact
          ⟨footprint_combine₂
            (mergeProduct_symbols_subset _ _) hSymL hSymR
            hBaseOne hBaseTwo
            (flagNames_mono (subsetAppendLeft _ _))
            (flagNames_mono (subsetAppendRight _ _)),
          footprint_combine₂
            (mergeProduct_assignedSymbols_subset _ _)
            hAsgL hAsgR hAsgBaseOne hAsgBaseTwo
            (flagNames_mono (subsetAppendLeft _ _))
            (flagNames_mono (subsetAppendRight _ _))⟩
      · rw [seqResult_eq_general s k C₁ C₂ r₁ r₂ h₁
            h₂ h₃]
        set m := k + (r₁.ids ++ r₂.ids).length with hm
        set Ψ : List Nat :=
          r₁.ids ++ r₂.ids ++
            [flagAt s m, flagAt s (m + 1)] with hΨ
        have hSubOne : r₁.ids ⊆ Ψ := by
          intro x hx
          simp only [hΨ, List.mem_append]
          exact Or.inl (Or.inl hx)
        have hSubTwo : r₂.ids ⊆ Ψ := by
          intro x hx
          simp only [hΨ, List.mem_append]
          exact Or.inl (Or.inr hx)
        have hFlags :
            ({flagName (flagAt s m),
                flagName (flagAt s (m + 1))} :
              Finset ProgramNames) ⊆ flagNames Ψ := by
          intro X hX
          rcases Finset.mem_insert.mp hX with hEq | hEq
          · rw [hEq]
            refine mem_flagNames_iff.mpr ?_
            simp only [hΨ, List.mem_append]
            exact Or.inr (by simp)
          · rw [Finset.mem_singleton.mp hEq]
            refine mem_flagNames_iff.mpr ?_
            simp only [hΨ, List.mem_append]
            exact Or.inr (by simp)
        refine ⟨?_, ?_⟩
        · refine
            footprint_combine
              (mergeGeneral_symbols_subset _ _ _ _ _)
              hSymL hSymR hBaseOne hBaseTwo
              (flagNames_mono hSubOne)
              (flagNames_mono hSubTwo) ?_
          intro X hX
          exact Finset.mem_union_right _ (hFlags hX)
        · refine
            footprint_combine
              (mergeGeneral_assignedSymbols_subset _ _ _ _
                _)
              hAsgL hAsgR hAsgBaseOne hAsgBaseTwo
              (flagNames_mono hSubOne)
              (flagNames_mono hSubTwo) ?_
          intro X hX
          exact Finset.mem_union_right _ (hFlags hX)

end Preprocess

end Whiel

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}
variable (s : FlagSupply Γ)

/- Lemma "Footprint" for one conditional node. -/
theorem iteResult_footprint
    (k : Nat) (G : Guard D Γ) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (hSymOne :
      r₁.loop.unfold.symbols ⊆
        C₁.symbols ∪ flagNames r₁.ids)
    (hAsgOne :
      r₁.loop.unfold.assignedSymbols ⊆
        C₁.assignedSymbols ∪ flagNames r₁.ids)
    (hSymTwo :
      r₂.loop.unfold.symbols ⊆
        C₂.symbols ∪ flagNames r₂.ids)
    (hAsgTwo :
      r₂.loop.unfold.assignedSymbols ⊆
        C₂.assignedSymbols ∪ flagNames r₂.ids) :
    (iteResult s k G C₁ C₂
          r₁ r₂).loop.unfold.symbols ⊆
        (Cmd.ite G C₁ C₂).symbols ∪
          flagNames (iteResult s k G C₁ C₂ r₁ r₂).ids ∧
      (iteResult s k G C₁ C₂
            r₁ r₂).loop.unfold.assignedSymbols ⊆
        (Cmd.ite G C₁ C₂).assignedSymbols ∪
          flagNames
            (iteResult s k G C₁ C₂ r₁ r₂).ids := by
  have hSymL :
      (seqLeft r₁ r₂).unfold.symbols ⊆
        C₁.symbols ∪ flagNames r₁.ids := by
    rw [seqLeft_symbols]; exact hSymOne
  have hSymR :
      (seqRight r₁ r₂).unfold.symbols ⊆
        C₂.symbols ∪ flagNames r₂.ids := by
    rw [seqRight_symbols]; exact hSymTwo
  have hAsgL :
      (seqLeft r₁ r₂).unfold.assignedSymbols ⊆
        C₁.assignedSymbols ∪ flagNames r₁.ids := by
    rw [seqLeft_assignedSymbols]; exact hAsgOne
  have hAsgR :
      (seqRight r₁ r₂).unfold.assignedSymbols ⊆
        C₂.assignedSymbols ∪ flagNames r₂.ids := by
    rw [seqRight_assignedSymbols]; exact hAsgTwo
  set m := k + (r₁.ids ++ r₂.ids).length with hm
  set Ψ : List Nat :=
    r₁.ids ++ r₂.ids ++ [flagAt s m] with hΨ
  have hSubOne : r₁.ids ⊆ Ψ := by
    intro x hx
    simp only [hΨ, List.mem_append]
    exact Or.inl (Or.inl hx)
  have hSubTwo : r₂.ids ⊆ Ψ := by
    intro x hx
    simp only [hΨ, List.mem_append]
    exact Or.inl (Or.inr hx)
  have hFlag :
      flagName (flagAt s m) ∈ flagNames Ψ := by
    refine mem_flagNames_iff.mpr ?_
    simp only [hΨ, List.mem_append]
    exact Or.inr (by simp)
  refine ⟨?_, ?_⟩
  · refine
      footprint_combine
        (hoistIte_symbols_subset _ _ _ _ _ _ _) hSymL
        hSymR ?_ ?_ (flagNames_mono hSubOne)
        (flagNames_mono hSubTwo) ?_
    · intro X hX
      simp only [Cmd.symbols, Finset.mem_union]
      tauto
    · intro X hX
      simp only [Cmd.symbols, Finset.mem_union]
      tauto
    · intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · refine Finset.mem_union_left _ ?_
        rw [Guard.symbols_onExtension] at h
        simp only [Cmd.symbols, Finset.mem_union]
        tauto
      · rw [Finset.mem_singleton] at h
        rw [h, drawnFlag_sym_val]
        exact Finset.mem_union_right _ hFlag
  · refine
      footprint_combine
        (hoistIte_assignedSymbols_subset _ _ _ _ _ _ _)
        hAsgL hAsgR ?_ ?_ (flagNames_mono hSubOne)
        (flagNames_mono hSubTwo) ?_
    · intro X hX
      simp only [Cmd.assignedSymbols, Finset.mem_union]
      tauto
    · intro X hX
      simp only [Cmd.assignedSymbols, Finset.mem_union]
      tauto
    · intro X hX
      rw [Finset.mem_singleton] at hX
      rw [hX, drawnFlag_sym_val]
      exact Finset.mem_union_right _ hFlag

/- Lemma "Footprint" for one nested loop. -/
theorem loopResult_footprint
    (k : Nat) (G : Guard D Γ) (C₀ : Cmd D Γ)
    (r₀ : NormResult D Γ)
    (hSym :
      r₀.loop.unfold.symbols ⊆
        C₀.symbols ∪ flagNames r₀.ids)
    (hAsg :
      r₀.loop.unfold.assignedSymbols ⊆
        C₀.assignedSymbols ∪ flagNames r₀.ids) :
    (loopResult s k G r₀).loop.unfold.symbols ⊆
        (Cmd.«while» G C₀).symbols ∪
          flagNames (loopResult s k G r₀).ids ∧
      (loopResult s k G r₀).loop.unfold.assignedSymbols ⊆
        (Cmd.«while» G C₀).assignedSymbols ∪
          flagNames (loopResult s k G r₀).ids := by
  set m := k + r₀.ids.length with hm
  set Ψ : List Nat := r₀.ids ++ [flagAt s m] with hΨ
  have hSub : r₀.ids ⊆ Ψ := subsetAppendLeft _ _
  have hFlag :
      flagName (flagAt s m) ∈ flagNames Ψ := by
    refine mem_flagNames_iff.mpr ?_
    simp only [hΨ, List.mem_append]
    exact Or.inr (by simp)
  refine ⟨?_, ?_⟩
  · refine
      footprint_combine_one
        (flattenGeneral_symbols_subset _ _ _ _) hSym ?_
        (flagNames_mono hSub) ?_
    · intro X hX
      simp only [Cmd.symbols, Finset.mem_union]
      tauto
    · intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · refine Finset.mem_union_left _ ?_
        rw [Guard.symbols_onExtension] at h
        simp only [Cmd.symbols, Finset.mem_union]
        tauto
      · rw [Finset.mem_singleton] at h
        rw [h, drawnFlag_sym_val]
        exact Finset.mem_union_right _ hFlag
  · refine
      footprint_combine_one
        (flattenGeneral_assignedSymbols_subset _ _ _ _) hAsg
        ?_ (flagNames_mono hSub) ?_
    · intro X hX
      exact hX
    · intro X hX
      rw [Finset.mem_singleton] at hX
      rw [hX, drawnFlag_sym_val]
      exact Finset.mem_union_right _ hFlag

/-
  Lemma "Footprint": the only relations the recursion adds
  to a command's symbols and assigned sets are the flags it
  draws.
-/
theorem normalizeAux_footprint s
    (k : Nat)
    (C : Cmd D Γ) :
    (normalizeAux s k C).loop.unfold.symbols ⊆
        C.symbols ∪ flagNames (normalizeAux s k C).ids ∧
      (normalizeAux s k C).loop.unfold.assignedSymbols ⊆
        C.assignedSymbols ∪
          flagNames (normalizeAux s k C).ids := by
  have hBase :
      ∀ C' : Cmd D Γ,
        (baseResult C').loop.unfold.symbols ⊆
            C'.symbols ∪
              flagNames (baseResult C').ids ∧
          (baseResult C').loop.unfold.assignedSymbols ⊆
            C'.assignedSymbols ∪
              flagNames (baseResult C').ids := by
    intro C'
    constructor
    · intro X hX
      rw [baseResult_symbols] at hX
      exact Finset.mem_union_left _ hX
    · intro X hX
      rw [baseResult_assignedSymbols] at hX
      exact Finset.mem_union_left _ hX
  induction C generalizing k with
  | skip => exact hBase _
  | assign X e => exact hBase _
  | seq C₁ C₂ ih₁ ih₂ =>
      by_cases hFree : LoopFree (Cmd.seq C₁ C₂)
      · rw [normalizeAux_eq_base_seq s k hFree]
        exact hBase _
      · rw [normalizeAux_eq_seq s k hFree]
        exact
          seqResult_footprint s k C₁ C₂ _ _ (ih₁ k).1
            (ih₁ k).2 (ih₂ (k + flagBudget C₁)).1
            (ih₂ (k + flagBudget C₁)).2
  | ite G C₁ C₂ ih₁ ih₂ =>
      by_cases hFree : LoopFree (Cmd.ite G C₁ C₂)
      · rw [normalizeAux_eq_base_ite s k hFree]
        exact hBase _
      · rw [normalizeAux_eq_ite s k hFree]
        exact
          iteResult_footprint s k G C₁ C₂ _ _ (ih₁ k).1
            (ih₁ k).2 (ih₂ (k + flagBudget C₁)).1
            (ih₂ (k + flagBudget C₁)).2
  | «while» G C₀ ih =>
      by_cases hIdem : idemCheck G C₀ = true
      · rw [normalizeAux_eq_idem s k hIdem]
        refine ⟨?_, ?_⟩
        · intro X hX
          rcases Finset.mem_union.mp ((ih k).1 hX) with
            h | h
          · refine Finset.mem_union_left _ ?_
            simp only [Cmd.symbols, Finset.mem_union]
            tauto
          · exact Finset.mem_union_right _ h
        · intro X hX
          exact (ih k).2 hX
      · by_cases hLF : LoopFree C₀
        · rw [normalizeAux_eq_loopFreeBody s k hIdem hLF]
          refine ⟨?_, ?_⟩
          · intro X hX
            rw [loopFreeResult_symbols] at hX
            refine Finset.mem_union_left _ ?_
            have h :=
              flattenLoopFree_symbols_subset G C₀ hX
            simp only [Cmd.symbols, Finset.mem_union]
            simp only [Finset.mem_union] at h
            tauto
          · intro X hX
            rw [loopFreeResult_assignedSymbols] at hX
            exact Finset.mem_union_left _
              (flattenLoopFree_assignedSymbols_subset G C₀
                hX)
        · rw [normalizeAux_eq_flatten s k hIdem hLF]
          exact
            loopResult_footprint s k G C₀ _ (ih k).1
              (ih k).2

/-
  Lemma "Footprint" for the normalizer, after the final
  clean: the clean reads no new relation and assigns exactly
  the same ones, so both inclusions carry through.
-/
theorem normalize_footprint
    (C : Cmd D Γ) :
    (normalize C).loop.unfold.symbols ⊆
        C.symbols ∪ flagNames (normalize C).ids ∧
      (normalize C).loop.unfold.assignedSymbols ⊆
        C.assignedSymbols ∪
          flagNames (normalize C).ids := by
  have hRaw :=
    normalizeAux_footprint (FlagSupply.initial Γ) 0 C
  refine ⟨?_, ?_⟩
  · refine
      subset_trans
        (Framed.symbols_unfold_clean_subset _) hRaw.1
  · rw [show
        (normalize C).loop.unfold.assignedSymbols =
          (normalizeRaw C).loop.unfold.assignedSymbols from
        Framed.assignedSymbols_unfold_clean _]
    exact hRaw.2

end Preprocess

end Whiel

------------------------------------------------------------
-- The Three Congruence Steps
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- A big-step equivalent target keeps the equivalence. -/
theorem EquivMod.trans_bigStepEquiv
    {hExt : Ω.extensionOf Δ}
    {C : Cmd D Δ}
    {W V : Cmd D Ω}
    (hEquiv : EquivMod hExt C W)
    (hEq : Cmd.BigStepEquiv W V) :
    EquivMod hExt C V := by
  constructor
  · intro s t hRun
    rcases hEquiv.simulates s t hRun with ⟨v, hV, hVR⟩
    exact ⟨v, (hEq s v).mp hV, hVR⟩
  · intro s t hRun
    exact hEquiv.projectRun ((hEq s t).mpr hRun)

/- A big-step equivalent source keeps the equivalence. -/
theorem EquivMod.of_bigStepEquiv_left
    {hExt : Ω.extensionOf Δ}
    {C C' : Cmd D Δ}
    {W : Cmd D Ω}
    (hEq : Cmd.BigStepEquiv C C')
    (hEquiv : EquivMod hExt C' W) :
    EquivMod hExt C W := by
  constructor
  · intro s t hRun
    exact hEquiv.simulates s t ((hEq _ t).mp hRun)
  · intro s t hRun
    exact (hEq _ _).mpr (hEquiv.projectRun hRun)

/-
  The sequence congruence, in the arbitrary-start form:
  the second hypothesis is used at the intermediate state,
  which is not a lifted one.
-/
theorem equivMod_seq
    (hExt : Ω.extensionOf Δ)
    {C₁ C₂ : Cmd D Δ}
    {W₁ W₂ : Cmd D Ω}
    (h₁ : EquivMod hExt C₁ W₁)
    (h₂ : EquivMod hExt C₂ W₂) :
    EquivMod hExt (.seq C₁ C₂) (.seq W₁ W₂) := by
  constructor
  · intro s t hRun
    rcases (Cmd.bigStep_seq_iff _ _ _ _).mp hRun with
      ⟨x, hOne, hTwo⟩
    rcases h₁.simulates s x hOne with ⟨u, hU, hUR⟩
    rcases h₂.simulates u t (by rw [hUR]; exact hTwo) with
      ⟨v, hV, hVR⟩
    exact ⟨v, Cmd.BigStep.seq hU hV, hVR⟩
  · intro s t hRun
    rcases (Cmd.bigStep_seq_iff _ _ _ _).mp hRun with
      ⟨u, hU, hV⟩
    exact Cmd.BigStep.seq (h₁.projectRun hU)
      (h₂.projectRun hV)

/- The conditional congruence: both sides take the same
   branch, because the source guard is over the smaller
   schema. -/
theorem equivMod_ite
    (hExt : Ω.extensionOf Δ)
    (G : Guard D Δ)
    {C₁ C₂ : Cmd D Δ}
    {W₁ W₂ : Cmd D Ω}
    (h₁ : EquivMod hExt C₁ W₁)
    (h₂ : EquivMod hExt C₂ W₂) :
    EquivMod hExt (.ite G C₁ C₂)
      (.ite (G.onExtension hExt) W₁ W₂) := by
  constructor
  · intro s t hRun
    rcases (Cmd.bigStep_ite_iff _ _ _ _ _).mp hRun with
      hT | hF
    · rcases h₁.simulates s t hT.2 with ⟨v, hV, hVR⟩
      exact
        ⟨v,
          Cmd.BigStep.ite_true
            ((retag_eval_iff hExt G s).mpr hT.1) hV,
          hVR⟩
    · rcases h₂.simulates s t hF.2 with ⟨v, hV, hVR⟩
      refine ⟨v, Cmd.BigStep.ite_false ?_ hV, hVR⟩
      intro hEval
      exact hF.1 ((retag_eval_iff hExt G s).mp hEval)
  · intro s t hRun
    rcases (Cmd.bigStep_ite_iff _ _ _ _ _).mp hRun with
      hT | hF
    · exact
        Cmd.BigStep.ite_true
          ((retag_eval_iff hExt G s).mp hT.1)
          (h₁.projectRun hT.2)
    · refine
        Cmd.BigStep.ite_false ?_ (h₂.projectRun hF.2)
      intro hEval
      exact hF.1 ((retag_eval_iff hExt G s).mpr hEval)

/-
  The loop congruence. The second iteration begins at the
  state the first one ended in, which carries whatever
  flags the body left up; this is the step a lifted-start
  hypothesis cannot take.
-/
theorem equivMod_while
    (hExt : Ω.extensionOf Δ)
    (G : Guard D Δ)
    {C₀ : Cmd D Δ}
    {W₀ : Cmd D Ω}
    (hBody : EquivMod hExt C₀ W₀) :
    EquivMod hExt (.«while» G C₀)
      (.«while» (G.onExtension hExt) W₀) := by
  have hLift :
      ∀ {a b : Instance D Δ},
        Cmd.BigStep (.«while» G C₀) a b →
          ∀ s : Instance D Ω, project hExt s = a →
            ∃ t : Instance D Ω,
              Cmd.BigStep
                  (.«while» (G.onExtension hExt) W₀) s
                  t ∧
                project hExt t = b := by
    intro a b hStep
    generalize hW :
        (Cmd.«while» G C₀ : Cmd D Δ) = W at hStep
    induction hStep with
    | skip I => cases hW
    | assign I X e => cases hW
    | seq h₁ h₂ ih₁ ih₂ => cases hW
    | ite_true hEval hRun ih => cases hW
    | ite_false hEval hRun ih => cases hW
    | @while_false G' B' a hFalse =>
        cases hW
        intro s hProj
        refine ⟨s, Cmd.BigStep.while_false ?_, hProj⟩
        intro hEval
        refine hFalse ?_
        rw [← hProj]
        exact (retag_eval_iff hExt G s).mp hEval
    | @while_true G' B' a x b hEval hRun hLoop ihRun
        ihLoop =>
        cases hW
        intro s hProj
        rcases
          hBody.simulates s x
            (by rw [hProj]; exact hRun) with
          ⟨u, hU, hUR⟩
        rcases ihLoop rfl u hUR with ⟨v, hV, hVR⟩
        refine ⟨v, ?_, hVR⟩
        refine Cmd.BigStep.while_true ?_ hU hV
        refine (retag_eval_iff hExt G s).mpr ?_
        rw [hProj]
        exact hEval
  have hProject :
      ∀ {s t : Instance D Ω},
        Cmd.BigStep (.«while» (G.onExtension hExt) W₀) s
            t →
          Cmd.BigStep (.«while» G C₀) (project hExt s)
            (project hExt t) := by
    intro s t hStep
    generalize hW :
        (Cmd.«while» (G.onExtension hExt) W₀ :
          Cmd D Ω) = W at hStep
    induction hStep with
    | skip I => cases hW
    | assign I X e => cases hW
    | seq h₁ h₂ ih₁ ih₂ => cases hW
    | ite_true hEval hRun ih => cases hW
    | ite_false hEval hRun ih => cases hW
    | @while_false Gu Bo s hFalse =>
        cases hW
        refine Cmd.BigStep.while_false ?_
        intro hEval
        exact hFalse ((retag_eval_iff hExt G s).mpr hEval)
    | @while_true Gu Bo s u t hEval hRun hLoop ihRun
        ihLoop =>
        cases hW
        exact
          Cmd.BigStep.while_true
            ((retag_eval_iff hExt G s).mp hEval)
            (hBody.projectRun hRun) (ihLoop rfl)
  exact
    ⟨fun s t hRun => hLift hRun s rfl,
      fun _ _ hRun => hProject hRun⟩

/- Retagging a framed loop keeps the base shape. -/
theorem isBase_retagOn
    (hExt : Ω.extensionOf Δ)
    {L : Framed D Δ}
    (hBase : L.IsBase) :
    (L.retagOn hExt).IsBase := by
  obtain ⟨hInit, hGuard, hBody⟩ := hBase
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Framed.retagOn, hInit, hGuard, hBody,
      retag, Guard.onExtension]

end Preprocess

end Whiel

------------------------------------------------------------
-- Symbols Lie In The Schema
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

theorem guard_symbols_subset_syms
    (G : Guard D Γ) :
    G.symbols ⊆ Γ.syms := by
  induction G with
  | «true» => intro X hX; cases hX
  | «false» => intro X hX; cases hX
  | eq e₁ e₂ =>
      intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · exact RAExpr.symbols_subset e₁ h
      · exact RAExpr.symbols_subset e₂ h
  | subset e₁ e₂ =>
      intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · exact RAExpr.symbols_subset e₁ h
      · exact RAExpr.symbols_subset e₂ h
  | and φ ψ ihφ ihψ =>
      intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · exact ihφ h
      · exact ihψ h
  | or φ ψ ihφ ihψ =>
      intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · exact ihφ h
      · exact ihψ h
  | not φ ih => exact ih

theorem cmd_symbols_subset_syms
    (C : Cmd D Γ) :
    C.symbols ⊆ Γ.syms := by
  induction C with
  | skip => intro X hX; cases hX
  | assign Y e =>
      intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · rw [Finset.mem_singleton.mp h]
        exact Y.2
      · exact RAExpr.symbols_subset e h
  | seq C₁ C₂ ih₁ ih₂ =>
      intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · exact ih₁ h
      · exact ih₂ h
  | ite G C₁ C₂ ih₁ ih₂ =>
      intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact guard_symbols_subset_syms G h
        · exact ih₁ h
      · exact ih₂ h
  | «while» G C ih =>
      intro X hX
      rcases Finset.mem_union.mp hX with h | h
      · exact guard_symbols_subset_syms G h
      · exact ih h

end Preprocess

end Whiel

------------------------------------------------------------
-- Freshness And Independence Of The Drawn Flags
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}
variable (s : FlagSupply Γ)

/- The identifiers of a binary node's two sub-calls. -/
theorem seqPair_ids
    (k : Nat)
    (C₁ C₂ : Cmd D Γ) :
    (normalizeAux s k C₁).ids ++
        (normalizeAux s (k + flagBudget C₁) C₂).ids =
      flagIds (flagAt s k)
        (flagBudget C₁ + flagBudget C₂) := by
  rw [normalizeAux_ids, normalizeAux_ids, flagAt_add,
    flagIds_append]

theorem flagAt_not_mem_flagIds
    (k n j : Nat)
    (hj : n ≤ j) :
    flagAt s (k + j) ∉ flagIds (flagAt s k) n := by
  rw [flagAt_add]
  intro hMem
  rw [mem_flagIds_iff] at hMem
  omega

theorem normalizeAux_ids_ge s
    (k : Nat) (C : Cmd D Γ) {i : Nat}
    (hMem : i ∈ (normalizeAux s k C).ids) :
    flagAt s k ≤ i := by
  rw [normalizeAux_ids, mem_flagIds_iff] at hMem
  exact hMem.1

theorem normalizeAux_ids_lt s
    (k : Nat) (C : Cmd D Γ) {i : Nat}
    (hMem : i ∈ (normalizeAux s k C).ids) :
    i < flagAt s k + flagBudget C := by
  rw [normalizeAux_ids, mem_flagIds_iff] at hMem
  exact hMem.2

theorem normalizeAux_ids_fresh s
    (k : Nat) (C : Cmd D Γ) {i : Nat}
    (hMem : i ∈ (normalizeAux s k C).ids) :
    flagName i ∉ Γ.syms := by
  refine flagName_not_mem_of_flagSeed_le ?_
  have h := normalizeAux_ids_ge s k C hMem
  have hBound := s.bound
  simp only [flagAt] at h
  omega

/- A drawn flag is fresh for the schema it extends. -/
theorem drawnFlag_fresh
    {Φ Ψ : List Nat}
    {j : Nat}
    (hMem : flagAt s j ∈ Ψ)
    (hNot : flagAt s j ∉ Φ) :
    (drawnFlag s Ψ j hMem).sym.1 ∉
      (flagExt Γ Φ).syms := by
  rw [drawnFlag_sym_val]
  intro hIn
  rcases Finset.mem_union.mp hIn with h | h
  · exact flagName_flagAt_not_mem s j h
  · exact hNot (mem_flagNames_iff.mp h)

/- Two drawn flags at different offsets are distinct. -/
theorem drawnFlag_ne
    {Ψ : List Nat}
    {j₁ j₂ : Nat}
    (h₁ : flagAt s j₁ ∈ Ψ)
    (h₂ : flagAt s j₂ ∈ Ψ)
    (hNe : j₁ ≠ j₂) :
    (drawnFlag s Ψ j₁ h₁).sym ≠
      (drawnFlag s Ψ j₂ h₂).sym := by
  intro hEq
  have hName :
      flagName (flagAt s j₁) = flagName (flagAt s j₂) :=
    congrArg (fun X : (flagExt Γ Ψ).syms => X.1) hEq
  have hId : flagAt s j₁ = flagAt s j₂ :=
    flagName_injective hName
  simp only [flagAt] at hId
  omega

/-
  Independence of the sources gives independence of the
  framed loops: by the footprint lemma the only symbols the
  recursion adds are flags, and the two flag sets are
  disjoint.
-/
theorem independent_of_source
    {Ω : UnnamedSchema ProgramNames}
    {C₁ C₂ : Cmd D Γ}
    {W₁ W₂ : Cmd D Ω}
    {Φ₁ Φ₂ : List Nat}
    (hIndep : Independent C₁ C₂)
    (hSymOne :
      W₁.symbols ⊆ C₁.symbols ∪ flagNames Φ₁)
    (hAsgOne :
      W₁.assignedSymbols ⊆
        C₁.assignedSymbols ∪ flagNames Φ₁)
    (hSymTwo :
      W₂.symbols ⊆ C₂.symbols ∪ flagNames Φ₂)
    (hAsgTwo :
      W₂.assignedSymbols ⊆
        C₂.assignedSymbols ∪ flagNames Φ₂)
    (hFreshOne : ∀ i ∈ Φ₁, flagName i ∉ Γ.syms)
    (hFreshTwo : ∀ i ∈ Φ₂, flagName i ∉ Γ.syms)
    (hDisj : ∀ i ∈ Φ₁, i ∉ Φ₂) :
    Independent W₁ W₂ := by
  constructor
  · intro X hX hMem
    rcases Finset.mem_union.mp (hAsgOne hX) with hA | hA
    · rcases Finset.mem_union.mp (hSymTwo hMem) with
        hB | hB
      · exact hIndep.1 X hA hB
      · rcases (mem_flagNames Φ₂ X).mp hB with
          ⟨i, hi, hEq⟩
        refine hFreshTwo i hi ?_
        rw [hEq]
        exact Cmd.assignedSymbols_subset_syms C₁ hA
    · rcases (mem_flagNames Φ₁ X).mp hA with
        ⟨i, hi, hEq⟩
      rcases Finset.mem_union.mp (hSymTwo hMem) with
        hB | hB
      · refine hFreshOne i hi ?_
        rw [hEq]
        exact cmd_symbols_subset_syms C₂ hB
      · rcases (mem_flagNames Φ₂ X).mp hB with
          ⟨j, hj, hEqj⟩
        have hIJ : i = j :=
          flagName_injective (hEq.trans hEqj.symm)
        exact hDisj i hi (hIJ ▸ hj)
  · intro X hX hMem
    rcases Finset.mem_union.mp (hAsgTwo hX) with hA | hA
    · rcases Finset.mem_union.mp (hSymOne hMem) with
        hB | hB
      · exact hIndep.2 X hA hB
      · rcases (mem_flagNames Φ₁ X).mp hB with
          ⟨i, hi, hEq⟩
        refine hFreshOne i hi ?_
        rw [hEq]
        exact Cmd.assignedSymbols_subset_syms C₂ hA
    · rcases (mem_flagNames Φ₂ X).mp hA with
        ⟨i, hi, hEq⟩
      rcases Finset.mem_union.mp (hSymOne hMem) with
        hB | hB
      · refine hFreshTwo i hi ?_
        rw [hEq]
        exact cmd_symbols_subset_syms C₁ hB
      · rcases (mem_flagNames Φ₁ X).mp hB with
          ⟨j, hj, hEqj⟩
        have hIJ : j = i :=
          flagName_injective (hEqj.trans hEq.symm)
        exact hDisj j hj (hIJ ▸ hi)

/- Loop-free code normalizes to its base framed loop. -/
theorem normalizeAux_of_loopFree s
    (k : Nat)
    {C : Cmd D Γ}
    (hFree : LoopFree C) :
    normalizeAux s k C = baseResult C := by
  cases C with
  | skip => rfl
  | assign X e => rfl
  | seq C₁ C₂ => exact normalizeAux_eq_base_seq s k hFree
  | ite G C₁ C₂ => exact normalizeAux_eq_base_ite s k hFree
  | «while» G C₀ =>
      exact absurd hFree (not_loopFree_while G C₀)

theorem baseResult_loop_isBase
    (C : Cmd D Γ) :
    (baseResult C).loop.IsBase :=
  isBase_retagOn _ (Framed.isBase_base C)

/- The idempotent-nesting test discards the outer loop. -/
theorem bigStepEquiv_of_idemCheck
    {G : Guard D Γ}
    {C₀ : Cmd D Γ}
    (hIdem : idemCheck G C₀ = true) :
    Cmd.BigStepEquiv (.«while» G C₀) C₀ := by
  cases C₀ with
  | skip => simp [idemCheck] at hIdem
  | assign X e => simp [idemCheck] at hIdem
  | seq C₁ C₂ => simp [idemCheck] at hIdem
  | ite G' C₁ C₂ => simp [idemCheck] at hIdem
  | «while» G' D₀ =>
      have hG : G' = G := eq_of_guardSame hIdem
      subst hG
      exact while_idem_bigStepEquiv G' D₀

end Preprocess

end Whiel

------------------------------------------------------------
-- The Normalization Theorem
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}
variable (s : FlagSupply Γ)

theorem baseResult_equivMod
    (C : Cmd D Γ) :
    EquivMod (flagExt_extensionOf Γ (baseResult C).ids) C
      (baseResult C).loop.unfold :=
  equivMod_retag_of_bigStepEquiv _
    (fun I J => (Framed.bigStep_base_iff C I J).symm)

/- The sequence clause is correct in all four cases. -/
theorem seqResult_equivMod
    (k : Nat) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (hOne :
      EquivMod (flagExt_extensionOf Γ r₁.ids) C₁
        r₁.loop.unfold)
    (hTwo :
      EquivMod (flagExt_extensionOf Γ r₂.ids) C₂
        r₂.loop.unfold)
    (hBaseOne : LoopFree C₁ → r₁.loop.IsBase)
    (hBaseTwo : LoopFree C₂ → r₂.loop.IsBase)
    (hIndep :
      independentCheck C₁ C₂ = true →
        Independent (seqLeft r₁ r₂).unfold
          (seqRight r₁ r₂).unfold)
    (hFreshOne :
      flagAt s (k + (r₁.ids ++ r₂.ids).length) ∉
        r₁.ids ++ r₂.ids)
    (hFreshTwo :
      flagAt s (k + (r₁.ids ++ r₂.ids).length + 1) ∉
        r₁.ids ++ r₂.ids) :
    EquivMod
      (flagExt_extensionOf Γ
        (seqResult s k C₁ C₂ r₁ r₂).ids)
      (Cmd.seq C₁ C₂)
      (seqResult s k C₁ C₂ r₁ r₂).loop.unfold := by
  have hL :
      EquivMod (flagExt_extensionOf Γ (r₁.ids ++ r₂.ids))
        C₁ (seqLeft r₁ r₂).unfold :=
    EquivMod.compose hOne
      (equivMod_retag
        (flagExt_mono Γ (subsetAppendLeft _ _))
        r₁.loop.unfold)
  have hR :
      EquivMod (flagExt_extensionOf Γ (r₁.ids ++ r₂.ids))
        C₂ (seqRight r₁ r₂).unfold :=
    EquivMod.compose hTwo
      (equivMod_retag
        (flagExt_mono Γ (subsetAppendRight _ _))
        r₂.loop.unfold)
  have hCong :
      EquivMod (flagExt_extensionOf Γ (r₁.ids ++ r₂.ids))
        (Cmd.seq C₁ C₂)
        (.seq (seqLeft r₁ r₂).unfold
          (seqRight r₁ r₂).unfold) :=
    equivMod_seq _ hL hR
  by_cases h₁ : LoopFree C₁
  · rw [seqResult_eq_intoPrefix s k C₁ C₂ r₁ r₂ h₁]
    exact
      hCong.trans_bigStepEquiv
        (mergeIntoPrefix_bigStepEquiv
          (isBase_retagOn _ (hBaseOne h₁)))
  · by_cases h₂ : LoopFree C₂
    · rw [seqResult_eq_intoSuffix s k C₁ C₂ r₁ r₂ h₁
          h₂]
      exact
        hCong.trans_bigStepEquiv
          (mergeIntoSuffix_bigStepEquiv
            (isBase_retagOn _ (hBaseTwo h₂)))
    · by_cases h₃ : independentCheck C₁ C₂ = true
      · rw [seqResult_eq_product s k C₁ C₂ r₁ r₂ h₁
            h₂ h₃]
        exact
          hCong.trans_bigStepEquiv
            (mergeProduct_bigStepEquiv (hIndep h₃))
      · rw [seqResult_eq_general s k C₁ C₂ r₁ r₂ h₁
            h₂ h₃]
        refine
          EquivMod.compose
            (hΩΔ :=
              flagExt_mono Γ (subsetAppendLeft _ _))
            hCong ?_
        exact
          mergeGeneral_equivMod _ _ _
            (drawnFlag_fresh s _ hFreshOne)
            (drawnFlag_fresh s _ hFreshTwo)
            (drawnFlag_ne s _ _ (by omega)) _ _

/- The conditional clause is correct. -/
theorem iteResult_equivMod
    (k : Nat) (G : Guard D Γ) (C₁ C₂ : Cmd D Γ)
    (r₁ r₂ : NormResult D Γ)
    (hOne :
      EquivMod (flagExt_extensionOf Γ r₁.ids) C₁
        r₁.loop.unfold)
    (hTwo :
      EquivMod (flagExt_extensionOf Γ r₂.ids) C₂
        r₂.loop.unfold)
    (hBaseOne : LoopFree C₁ → r₁.loop.IsBase)
    (hBaseTwo : LoopFree C₂ → r₂.loop.IsBase)
    (hFresh :
      flagAt s (k + (r₁.ids ++ r₂.ids).length) ∉
        r₁.ids ++ r₂.ids) :
    EquivMod
      (flagExt_extensionOf Γ
        (iteResult s k G C₁ C₂ r₁ r₂).ids)
      (Cmd.ite G C₁ C₂)
      (iteResult s k G C₁ C₂ r₁ r₂).loop.unfold := by
  have hL :
      EquivMod (flagExt_extensionOf Γ (r₁.ids ++ r₂.ids))
        C₁ (seqLeft r₁ r₂).unfold :=
    EquivMod.compose hOne
      (equivMod_retag
        (flagExt_mono Γ (subsetAppendLeft _ _))
        r₁.loop.unfold)
  have hR :
      EquivMod (flagExt_extensionOf Γ (r₁.ids ++ r₂.ids))
        C₂ (seqRight r₁ r₂).unfold :=
    EquivMod.compose hTwo
      (equivMod_retag
        (flagExt_mono Γ (subsetAppendRight _ _))
        r₂.loop.unfold)
  have hCong :
      EquivMod (flagExt_extensionOf Γ (r₁.ids ++ r₂.ids))
        (Cmd.ite G C₁ C₂)
        (.ite
          (G.onExtension
            (flagExt_extensionOf Γ (r₁.ids ++ r₂.ids)))
          (seqLeft r₁ r₂).unfold
          (seqRight r₁ r₂).unfold) :=
    equivMod_ite _ G hL hR
  refine
    EquivMod.compose
      (hΩΔ := flagExt_mono Γ (subsetAppendLeft _ _))
      hCong ?_
  refine hoistIte_equivMod _ _ ?_ _ _ _ _ _ ?_ ?_
  · exact drawnFlag_fresh s _ hFresh
  · intro hb
    exact
      isBase_retagOn _ (hBaseOne (of_decide_eq_true hb))
  · intro hb
    exact
      isBase_retagOn _ (hBaseTwo (of_decide_eq_true hb))

/- The flattening clause is correct. -/
theorem loopResult_equivMod
    (k : Nat) (G : Guard D Γ) (C₀ : Cmd D Γ)
    (r₀ : NormResult D Γ)
    (hBody :
      EquivMod (flagExt_extensionOf Γ r₀.ids) C₀
        r₀.loop.unfold)
    (hFresh : flagAt s (k + r₀.ids.length) ∉ r₀.ids) :
    EquivMod
      (flagExt_extensionOf Γ (loopResult s k G r₀).ids)
      (Cmd.«while» G C₀)
      (loopResult s k G r₀).loop.unfold := by
  have hCong :
      EquivMod (flagExt_extensionOf Γ r₀.ids)
        (Cmd.«while» G C₀)
        (.«while»
          (G.onExtension (flagExt_extensionOf Γ r₀.ids))
          r₀.loop.unfold) :=
    equivMod_while _ G hBody
  refine
    EquivMod.compose
      (hΩΔ := flagExt_mono Γ (subsetAppendLeft _ _))
      hCong ?_
  exact
    flattenGeneral_equivMod _ _
      (drawnFlag_fresh s _ hFresh) _
      _

/-
  The Normalization theorem: every command is equivalent
  modulo the flags the recursion draws to the unfolding of
  the framed loop the recursion returns, in the
  arbitrary-start form.
-/
theorem normalizeAux_equivMod s
    (k : Nat)
    (C : Cmd D Γ) :
    EquivMod
      (flagExt_extensionOf Γ (normalizeAux s k C).ids) C
      (normalizeAux s k C).loop.unfold := by
  induction C generalizing k with
  | skip => exact baseResult_equivMod _
  | assign X e => exact baseResult_equivMod _
  | seq C₁ C₂ ih₁ ih₂ =>
      by_cases hFree : LoopFree (Cmd.seq C₁ C₂)
      · rw [normalizeAux_eq_base_seq s k hFree]
        exact baseResult_equivMod _
      · rw [normalizeAux_eq_seq s k hFree]
        have hPair := seqPair_ids (D := D) s k C₁ C₂
        have hLen :
            ((normalizeAux s k C₁).ids ++
                (normalizeAux s (k + flagBudget C₁)
                  C₂).ids).length =
              flagBudget C₁ + flagBudget C₂ := by
          rw [hPair, length_flagIds]
        refine
          seqResult_equivMod s k C₁ C₂ _ _ (ih₁ k)
            (ih₂ (k + flagBudget C₁)) ?_ ?_ ?_ ?_ ?_
        · intro h
          rw [normalizeAux_of_loopFree s k h]
          exact baseResult_loop_isBase C₁
        · intro h
          rw [normalizeAux_of_loopFree s _ h]
          exact baseResult_loop_isBase C₂
        · intro hCheck
          refine
            independent_of_source
              (Φ₁ := (normalizeAux s k C₁).ids)
              (Φ₂ :=
                (normalizeAux s (k + flagBudget C₁) C₂).ids)
              (independent_of_check hCheck) ?_ ?_ ?_ ?_
              ?_ ?_ ?_
          · rw [seqLeft_symbols]
            exact (normalizeAux_footprint s k C₁).1
          · rw [seqLeft_assignedSymbols]
            exact (normalizeAux_footprint s k C₁).2
          · rw [seqRight_symbols]
            exact
              (normalizeAux_footprint s
                (k + flagBudget C₁) C₂).1
          · rw [seqRight_assignedSymbols]
            exact
              (normalizeAux_footprint s
                (k + flagBudget C₁) C₂).2
          · intro i hi
            exact normalizeAux_ids_fresh s k C₁ hi
          · intro i hi
            exact
              normalizeAux_ids_fresh s
                (k + flagBudget C₁) C₂ hi
          · intro i hi hj
            have h₁ := normalizeAux_ids_lt s k C₁ hi
            have h₂ :=
              normalizeAux_ids_ge s
                (k + flagBudget C₁) C₂ hj
            rw [flagAt_add] at h₂
            omega
        · rw [hLen, hPair]
          exact
            flagAt_not_mem_flagIds s k _ _ (Nat.le_refl _)
        · rw [hLen, hPair]
          exact
            flagAt_not_mem_flagIds s k
              (flagBudget C₁ + flagBudget C₂)
              (flagBudget C₁ + flagBudget C₂ + 1)
              (Nat.le_succ _)
  | ite G C₁ C₂ ih₁ ih₂ =>
      by_cases hFree : LoopFree (Cmd.ite G C₁ C₂)
      · rw [normalizeAux_eq_base_ite s k hFree]
        exact baseResult_equivMod _
      · rw [normalizeAux_eq_ite s k hFree]
        have hPair := seqPair_ids (D := D) s k C₁ C₂
        have hLen :
            ((normalizeAux s k C₁).ids ++
                (normalizeAux s (k + flagBudget C₁)
                  C₂).ids).length =
              flagBudget C₁ + flagBudget C₂ := by
          rw [hPair, length_flagIds]
        refine
          iteResult_equivMod s k G C₁ C₂ _ _ (ih₁ k)
            (ih₂ (k + flagBudget C₁)) ?_ ?_ ?_
        · intro h
          rw [normalizeAux_of_loopFree s k h]
          exact baseResult_loop_isBase C₁
        · intro h
          rw [normalizeAux_of_loopFree s _ h]
          exact baseResult_loop_isBase C₂
        · rw [hLen, hPair]
          exact
            flagAt_not_mem_flagIds s k _ _ (Nat.le_refl _)
  | «while» G C₀ ih =>
      by_cases hIdem : idemCheck G C₀ = true
      · rw [normalizeAux_eq_idem s k hIdem]
        exact
          EquivMod.of_bigStepEquiv_left
            (bigStepEquiv_of_idemCheck hIdem) (ih k)
      · by_cases hLF : LoopFree C₀
        · rw [normalizeAux_eq_loopFreeBody s k hIdem hLF]
          exact
            equivMod_retag_of_bigStepEquiv _
              (flattenLoopFree_bigStepEquiv G C₀)
        · rw [normalizeAux_eq_flatten s k hIdem hLF]
          refine loopResult_equivMod s k G C₀ _ (ih k) ?_
          rw [normalizeAux_ids, length_flagIds]
          exact
            flagAt_not_mem_flagIds s k _ _ (Nat.le_refl _)

/-
  The Normalization theorem for the normalizer: for every
  command over `Γ`, the unfolding of `⌊N(C)⌋` is a framed
  loop over `Γ[Φ]` with loop-free parts, and `C` is
  equivalent to it modulo `Φ`.
-/
theorem normalize_equivMod
    (C : Cmd D Γ) :
    EquivMod (flagExt_extensionOf Γ (normalize C).ids) C
      (normalize C).loop.unfold :=
  (normalizeAux_equivMod
      (FlagSupply.initial Γ) 0 C).trans_bigStepEquiv
    (Framed.bigStepEquiv_clean _)

/- The simulation half, which the transfer theorem uses. -/
theorem normalize_simulates
    (C : Cmd D Γ) :
    Simulates (flagExt_extensionOf Γ (normalize C).ids) C
      (normalize C).loop.unfold :=
  (normalize_equivMod C).simulates

end Preprocess

end Whiel

------------------------------------------------------------
-- The Output As A Program
------------------------------------------------------------

namespace Whiel

namespace Preprocess

open Whiel.Concrete

variable {D : Type} [Domain D]
variable {Γ : UnnamedSchema ProgramNames}

/-
  The paragraph "As a program" of the note's Section 5: the
  normalizer's output packaged in the repository's own sense
  of a program. Input and output schema are `Γ`, the
  execution schema is the flag extension `Γ[Φ]`, and the
  same extension witness serves for both, since the flag
  extension extends `Γ` by construction. The command is the
  cleaned unfolding.
-/
def NormResult.toProgram
    (r : NormResult D Γ) :
    Program D Γ Γ where
  execSchema := flagExt Γ r.ids
  extendsInput := flagExt_extensionOf Γ r.ids
  extendsOutput := flagExt_extensionOf Γ r.ids
  cmd := r.loop.unfold

@[simp] theorem NormResult.toProgram_cmd
    (r : NormResult D Γ) :
    r.toProgram.cmd = r.loop.unfold :=
  rfl

@[simp] theorem NormResult.toProgram_execSchema
    (r : NormResult D Γ) :
    r.toProgram.execSchema = flagExt Γ r.ids :=
  rfl

/-
  The program's `initialInstance` is the note's lift and its
  `observe` is the note's projection: the hidden relations
  are exactly the drawn flags, so entering with them empty
  is the lift, and the reduct to the output schema is the
  projection.
-/
@[simp] theorem NormResult.initialInstance_eq_lift
    (r : NormResult D Γ)
    (I : Instance D Γ) :
    r.toProgram.initialInstance I =
      lift (flagExt_extensionOf Γ r.ids) I :=
  rfl

@[simp] theorem NormResult.observe_eq_project
    (r : NormResult D Γ)
    (J : Instance D (flagExt Γ r.ids)) :
    r.toProgram.observe J =
      project (flagExt_extensionOf Γ r.ids) J :=
  rfl

/-
  Lemma "Program equivalence from lifted starts": an
  equivalence modulo the flags gives agreement of the
  packaged program with the source command, instantiating
  the arbitrary-start definition at a lifted state and using
  that the projection of a lift is the identity.
-/
theorem NormResult.bigStep_toProgram_iff_of_equivMod
    {r : NormResult D Γ}
    {C : Cmd D Γ}
    (hEquiv :
      EquivMod (flagExt_extensionOf Γ r.ids) C
        r.loop.unfold)
    (s t : Instance D Γ) :
    r.toProgram.BigStep s t ↔ Cmd.BigStep C s t := by
  constructor
  · rintro ⟨J, hRun, hObs⟩
    have hProject := hEquiv.projectRun hRun
    rw [NormResult.initialInstance_eq_lift,
      project_lift] at hProject
    rw [← hObs]
    exact hProject
  · intro hRun
    rcases
      hEquiv.simulates
        (lift (flagExt_extensionOf Γ r.ids) s) t
        (by rw [project_lift]; exact hRun) with
      ⟨t', hRun', hProj⟩
    exact ⟨t', hRun', hProj⟩

/-
  Definition "Program equivalence" for the normalizer: the
  packaged program agrees with its source command, so the
  two have exactly the same runs between `Γ`-instances.
-/
theorem normalize_toProgram_bigStep_iff
    (C : Cmd D Γ)
    (s t : Instance D Γ) :
    (normalize C).toProgram.BigStep s t ↔
      Cmd.BigStep C s t :=
  NormResult.bigStep_toProgram_iff_of_equivMod
    (normalize_equivMod C) s t

end Preprocess

end Whiel
