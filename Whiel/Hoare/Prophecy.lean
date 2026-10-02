-- Author: Jesse Comer
import Whiel.Hoare.Abstract
import Whiel.Cmd.Rewrites.TwoLoopFlat

/-
  Prophecy symbols: soundness of the leveled synthesis rule
  (Framework II of `reports/extended-synthesis`).

  Semantic, layer-A prototype. The program schema `Γ` is
  extended to `Ω`; the new names are the prophecy symbols.
  Clauses are semantic assertions over `Ω`. A candidate is
  a family of levels; level `j ≥ 1` may assume, through
  `prophecyBelow j`, the negated guard and the clauses of
  the levels below `j`, all evaluated at the collapsed
  state (IDBs replaced by their prophecy symbols); level
  `0` assumes nothing. The main theorem derives the
  `Γ`-triple of the loop from the leveled obligations: the
  ordinary while rule over `Ω` with the invariant
  `ladderInv`, in which the prophecy symbols are free
  relation symbols, then instantiation of the prophecy
  symbols to the exit state.

  Key declarations: `Instance.expandWith`,
  `Instance.ext_of_reduct_eq`,
  `Hoare.Prophecy.ProphecyCollapse`,
  `Hoare.Prophecy.prophecyOf`,
  `Hoare.Prophecy.levelsBelow`,
  `Hoare.Prophecy.prophecyBelow`,
  `Hoare.Prophecy.prophecyBelow_zero`,
  `Hoare.Prophecy.prophecyBelow_iff_prophecyOf`,
  `Hoare.Prophecy.ladderInv`,
  `Hoare.Prophecy.ladderInv_inductive`,
  `Hoare.Prophecy.obligations_of_ladderInv_inductive`,
  `Hoare.Prophecy.holdsAt_of_ladderInv`,
  `Hoare.Prophecy.hoareValid_while_of_leveled_vcs`,
  `Hoare.Prophecy.hoareValid_while_of_two_level_vcs`.
-/

------------------------------------------------------------
-- Instance Support
------------------------------------------------------------

namespace Instance

variable {A D : Type} {_ : RelationNames A} [Domain D]

/-
  The `Ω`-instance that agrees with `I` on the symbols of
  `Γ` and with `Z` on the new symbols of `Ω`. `Z` only
  supplies the new symbols; its `Γ`-part is discarded.
-/
def expandWith
    {Γ Ω : UnnamedSchema A}
    (hExt : Ω.extensionOf Γ)
    (I : Instance D Γ)
    (Z : Instance D Ω) :
    Instance D Ω := by
  intro X
  by_cases hX : X.1 ∈ Γ.syms
  · exact relationOfExtension hExt I X hX
  · exact Z X

/- Reducing an expansion recovers the original instance. -/
theorem reduct_expandWith
    {Γ Ω : UnnamedSchema A}
    (hExt : Ω.extensionOf Γ)
    (I : Instance D Γ)
    (Z : Instance D Ω) :
    reduct hExt (expandWith hExt I Z) = I := by
  apply Instance.ext
  intro s
  unfold reduct expandWith relationOfExtension
  simp [s.2]

/- New symbols of an expansion come from `Z`. -/
theorem expandWith_new
    {Γ Ω : UnnamedSchema A}
    (hExt : Ω.extensionOf Γ)
    (I : Instance D Γ)
    (Z : Instance D Ω)
    (X : Ω.syms)
    (hX : X.1 ∉ Γ.syms) :
    expandWith hExt I Z X = Z X := by
  simp [expandWith, hX]

/-
  Instances over an extension are determined by their
  reduct and their values on the new symbols.
-/
theorem ext_of_reduct_eq
    {Γ Ω : UnnamedSchema A}
    (hExt : Ω.extensionOf Γ)
    {J₁ J₂ : Instance D Ω}
    (hRed : reduct hExt J₁ = reduct hExt J₂)
    (hNew :
      ∀ X : Ω.syms, X.1 ∉ Γ.syms → J₁ X = J₂ X) :
    J₁ = J₂ := by
  apply Instance.ext
  intro X
  by_cases hX : X.1 ∈ Γ.syms
  · have h :
        reduct hExt J₁ ⟨X.1, hX⟩ =
          reduct hExt J₂ ⟨X.1, hX⟩ := by
      rw [hRed]
    simp only [reduct] at h
    exact (cast_inj _).mp h
  · exact hNew X hX

end Instance

------------------------------------------------------------
-- Prophecy Collapse
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace Prophecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/-
  The semantic content of the substitution `θ` and of the
  exit instantiation. `collapse J` is the state in which
  every IDB takes the value of its prophecy symbol; it
  depends only on the symbols the body does not assign.
  `exitLift I` is `I` with each prophecy symbol set to the
  exit value of its IDB, so it is a fixed point of
  `collapse`.
-/
structure ProphecyCollapse
    (hExt : Ω.extensionOf Γ)
    (assigned : Finset A) where
  collapse : Instance D Ω → Instance D Ω
  collapse_congr :
    ∀ J K : Instance D Ω,
      (∀ X : Ω.syms, X.1 ∉ assigned → J X = K X) →
        collapse J = collapse K
  exitLift : Instance D Γ → Instance D Ω
  reduct_exitLift :
    ∀ I : Instance D Γ,
      Instance.reduct hExt (exitLift I) = I
  collapse_exitLift :
    ∀ I : Instance D Γ,
      collapse (exitLift I) = exitLift I

end Prophecy

end Hoare

end Whiel

------------------------------------------------------------
-- Levels And Terminal Facts
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace Prophecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}
variable {hExt : Ω.extensionOf Γ}
variable {assigned : Finset A}

/-
  The note's `Ω(𝒦)`: the exit state fails the guard and
  satisfies every clause of `𝒦`, both evaluated at the
  collapsed state.
-/
def prophecyOf
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (K : List (Assertion D Ω))
    (J : Instance D Ω) : Prop :=
  ¬ (G.onExtension hExt).eval (gc.collapse J) ∧
    ∀ c ∈ K, c (gc.collapse J)

/- The clauses of the levels below `j`. -/
def levelsBelow
    (levels : Nat → List (Assertion D Ω))
    (j : Nat) : List (Assertion D Ω) :=
  (List.range j).flatMap levels

/- Membership in the levels below `j`. -/
theorem mem_levelsBelow_iff
    {levels : Nat → List (Assertion D Ω)}
    {j : Nat}
    {c : Assertion D Ω} :
    c ∈ levelsBelow levels j ↔
      ∃ i, i < j ∧ c ∈ levels i := by
  unfold levelsBelow
  simp [List.mem_flatMap, List.mem_range]

/-
  Terminal facts below level `j`: for `j ≥ 1`, the exit
  state fails the guard and satisfies every clause of a
  lower level, both evaluated at the collapsed state; level
  `0` assumes nothing (the note's `Ω_{<0} ≡ ⊤`).
-/
def prophecyBelow
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω))
    (j : Nat)
    (J : Instance D Ω) : Prop :=
  (0 < j → ¬ (G.onExtension hExt).eval (gc.collapse J)) ∧
    ∀ i, i < j → ∀ c ∈ levels i, c (gc.collapse J)

/- Level `0` has no terminal facts. -/
theorem prophecyBelow_zero
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω))
    (J : Instance D Ω) :
    prophecyBelow gc G levels 0 J := by
  refine ⟨?_, ?_⟩
  · intro h
    exact absurd h (Nat.lt_irrefl 0)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)

/- For `j ≥ 1`, `prophecyBelow j` is `Ω` of lower levels. -/
theorem prophecyBelow_iff_prophecyOf
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω))
    {j : Nat}
    (hj : 0 < j)
    (J : Instance D Ω) :
    prophecyBelow gc G levels j J ↔
      prophecyOf gc G (levelsBelow levels j) J := by
  unfold prophecyBelow prophecyOf
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁ hj, ?_⟩
    intro c hc
    obtain ⟨i, hi, hci⟩ := mem_levelsBelow_iff.mp hc
    exact h₂ i hi c hci
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun _ => h₁, ?_⟩
    intro i hi c hc
    exact h₂ c (mem_levelsBelow_iff.mpr ⟨i, hi, hc⟩)

/- Every clause of every level holds at `J`. -/
def holdsAt
    (levels : Nat → List (Assertion D Ω))
    (J : Instance D Ω) : Prop :=
  ∀ j, ∀ c ∈ levels j, c J

/-
  The prophecy-quantified invariant: each level holds
  whenever its terminal facts do.
-/
def ladderInv
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω)) :
    Assertion D Ω :=
  fun J =>
    ∀ j, prophecyBelow gc G levels j J →
      ∀ c ∈ levels j, c J

/- Terminal facts are monotone in the level. -/
theorem prophecyBelow_mono
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω))
    {i j : Nat}
    (hij : i ≤ j)
    {J : Instance D Ω}
    (h : prophecyBelow gc G levels j J) :
    prophecyBelow gc G levels i J := by
  refine ⟨fun hi => h.1 (Nat.lt_of_lt_of_le hi hij), ?_⟩
  intro k hk c hc
  exact h.2 k (Nat.lt_of_lt_of_le hk hij) c hc

/-
  Terminal facts depend only on the symbols the body does
  not assign.
-/
theorem prophecyBelow_congr
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω))
    (j : Nat)
    {J K : Instance D Ω}
    (hAgree :
      ∀ X : Ω.syms, X.1 ∉ assigned → J X = K X) :
    prophecyBelow gc G levels j J ↔
      prophecyBelow gc G levels j K := by
  unfold prophecyBelow
  rw [gc.collapse_congr J K hAgree]

/-
  At a collapse fixed point that fails the guard, the
  ladder invariant yields every level: the terminal facts
  of each level follow from the levels below it.
-/
theorem holdsAt_of_ladderInv
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω))
    {J : Instance D Ω}
    (hFix : gc.collapse J = J)
    (hNotG : ¬ (G.onExtension hExt).eval J)
    (hInv : ladderInv gc G levels J) :
    holdsAt levels J := by
  have hAll : ∀ j, prophecyBelow gc G levels j J := by
    intro j
    induction j with
    | zero =>
        exact prophecyBelow_zero gc G levels J
    | succ j ih =>
        refine ⟨?_, ?_⟩
        · intro _
          rw [hFix]
          exact hNotG
        intro i hi c hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact ih.2 i h c hc
        · subst h
          rw [hFix]
          exact hInv i ih c hc
  intro j c hc
  exact hInv j (hAll j) c hc

end Prophecy

end Hoare

end Whiel

------------------------------------------------------------
-- The Leveled Rule
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace Prophecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}
variable {assigned : Finset A}

/-
  Initiation of one clause at level `j`: the clause holds
  initially, given the terminal facts below `j`.
-/
def InitObligation
    (hExt : Ω.extensionOf Γ)
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω))
    (pre : Assertion D Γ)
    (j : Nat)
    (c : Assertion D Ω) : Prop :=
  ∀ J : Instance D Ω,
    pre (Instance.reduct hExt J) →
      prophecyBelow gc G levels j J → c J

/-
  Preservation of one clause at level `j`: the body
  re-establishes it, given the whole ladder invariant at
  the pre-state, the guard, and the terminal facts below
  `j`. (The note's rule assumes only the levels up to `j`
  at the pre-state; this is weaker, hence stronger as a
  rule.)
-/
def StepObligation
    (hExt : Ω.extensionOf Γ)
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (B : Cmd D Γ)
    (levels : Nat → List (Assertion D Ω))
    (j : Nat)
    (c : Assertion D Ω) : Prop :=
  ∀ J : Instance D Ω,
    ladderInv gc G levels J →
      (G.onExtension hExt).eval J →
        prophecyBelow gc G levels j J →
          wp (B.onExtension hExt) c J

/-
  Termination: at an exit state whose assigned relations
  equal their prophecy symbols, every clause implies the
  postcondition.
-/
def TermObligation
    (hExt : Ω.extensionOf Γ)
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (levels : Nat → List (Assertion D Ω))
    (post : Assertion D Γ) : Prop :=
  ∀ J : Instance D Ω,
    gc.collapse J = J →
      ¬ (G.onExtension hExt).eval J →
        holdsAt levels J →
          post (Instance.reduct hExt J)

/-
  Each level inductive relative to the levels below it
  makes the whole ladder inductive: the loop over `Ω`
  preserves `ladderInv`.
-/
theorem ladderInv_inductive
    (hExt : Ω.extensionOf Γ)
    {G : Guard D Γ}
    {B : Cmd D Γ}
    (gc : ProphecyCollapse (D := D) hExt B.assignedSymbols)
    (levels : Nat → List (Assertion D Ω))
    {pre : Assertion D Γ}
    (hInit :
      ∀ j, ∀ c ∈ levels j,
        InitObligation hExt gc G levels pre j c)
    (hStep :
      ∀ j, ∀ c ∈ levels j,
        StepObligation hExt gc G B levels j c) :
    HoareValid
      (fun J : Instance D Ω =>
        pre (Instance.reduct hExt J))
      (.while (G.onExtension hExt) (B.onExtension hExt))
      (Assertion.andNotGuard
        (ladderInv gc G levels) (G.onExtension hExt)) := by
  apply hoareValid_while_of_vcs
    (inv := ladderInv gc G levels)
  · intro J hPre j hOm c hc
    exact hInit j c hc J hPre hOm
  · intro J hJ K hStepK j hOmK c hc
    have hAgree :
        ∀ X : Ω.syms,
          X.1 ∉ B.assignedSymbols → J X = K X := by
      intro X hX
      exact
        (Cmd.onExtension_preserves_new_symbols
          hStepK X hX).symm
    have hOmJ : prophecyBelow gc G levels j J :=
      (prophecyBelow_congr gc G levels j hAgree).mpr hOmK
    exact hStep j c hc J hJ.1 hJ.2 hOmJ K hStepK
  · intro J hJ
    exact hJ

/-
  Converse of `ladderInv_inductive`: bulk initiation and
  preservation of `ladderInv` give back the per-clause
  obligations, so the per-clause form is exactly the
  inductiveness of the one invariant (the note's
  per-clause proposition).
-/
theorem obligations_of_ladderInv_inductive
    (hExt : Ω.extensionOf Γ)
    {G : Guard D Γ}
    {B : Cmd D Γ}
    (gc : ProphecyCollapse (D := D) hExt B.assignedSymbols)
    (levels : Nat → List (Assertion D Ω))
    {pre : Assertion D Γ}
    (hInit :
      Assertion.entails
        (fun J : Instance D Ω =>
          pre (Instance.reduct hExt J))
        (ladderInv gc G levels))
    (hMaint :
      Assertion.entails
        (Assertion.andGuard
          (ladderInv gc G levels) (G.onExtension hExt))
        (wp (B.onExtension hExt) (ladderInv gc G levels))) :
    (∀ j, ∀ c ∈ levels j,
      InitObligation hExt gc G levels pre j c) ∧
    (∀ j, ∀ c ∈ levels j,
      StepObligation hExt gc G B levels j c) := by
  refine ⟨?_, ?_⟩
  · intro j c hc J hPre hOm
    exact hInit J hPre j hOm c hc
  · intro j c hc J hInv hG hOm K hStepK
    have hAgree :
        ∀ X : Ω.syms,
          X.1 ∉ B.assignedSymbols → J X = K X := by
      intro X hX
      exact
        (Cmd.onExtension_preserves_new_symbols
          hStepK X hX).symm
    have hOmK : prophecyBelow gc G levels j K :=
      (prophecyBelow_congr gc G levels j hAgree).mp hOm
    exact hMaint J ⟨hInv, hG⟩ K hStepK j hOmK c hc

/-
  Soundness of the leveled rule (Theorem 3.3 of the note):
  the leveled obligations prove the loop's `Γ`-triple.
-/
theorem hoareValid_while_of_leveled_vcs
    (hExt : Ω.extensionOf Γ)
    {G : Guard D Γ}
    {B : Cmd D Γ}
    (gc : ProphecyCollapse (D := D) hExt B.assignedSymbols)
    (levels : Nat → List (Assertion D Ω))
    {pre post : Assertion D Γ}
    (hInit :
      ∀ j, ∀ c ∈ levels j,
        InitObligation hExt gc G levels pre j c)
    (hStep :
      ∀ j, ∀ c ∈ levels j,
        StepObligation hExt gc G B levels j c)
    (hTerm : TermObligation hExt gc G levels post) :
    HoareValid pre (.while G B) post := by
  intro I J hPre hRun
  let Z : Instance D Ω := gc.exitLift J
  let IΩ : Instance D Ω := Instance.expandWith hExt I Z
  have hRed : Instance.reduct hExt IΩ = I :=
    Instance.reduct_expandWith hExt I Z
  obtain ⟨JΩ, hRunΩ, hRedJ⟩ :=
    Cmd.onExtension_bigStep_lift hExt hRed hRun
  have hRunΩ' :
      Cmd.BigStep
        (.while (G.onExtension hExt) (B.onExtension hExt))
        IΩ JΩ :=
    hRunΩ
  have hLoop :=
    ladderInv_inductive hExt gc levels hInit hStep
  have hPreΩ : pre (Instance.reduct hExt IΩ) := by
    rw [hRed]
    exact hPre
  have hEnd :
      ladderInv gc G levels JΩ ∧
        ¬ (G.onExtension hExt).eval JΩ :=
    hLoop IΩ JΩ hPreΩ hRunΩ'
  have hNew :
      ∀ X : Ω.syms, X.1 ∉ Γ.syms → JΩ X = Z X := by
    intro X hX
    have hNotAssigned :
        X.1 ∉ (Cmd.while G B).assignedSymbols := by
      intro hIn
      exact hX ((Cmd.assignedSymbols_subset_syms _) hIn)
    rw [Cmd.onExtension_preserves_new_symbols
      hRunΩ X hNotAssigned]
    exact Instance.expandWith_new hExt I Z X hX
  have hJZ : JΩ = Z := by
    apply Instance.ext_of_reduct_eq hExt _ hNew
    rw [hRedJ, gc.reduct_exitLift]
  have hFix : gc.collapse JΩ = JΩ := by
    rw [hJZ]
    exact gc.collapse_exitLift J
  have hAll : holdsAt levels JΩ :=
    holdsAt_of_ladderInv gc G levels hFix hEnd.2 hEnd.1
  have hPost := hTerm JΩ hFix hEnd.2 hAll
  rw [hRedJ] at hPost
  exact hPost

end Prophecy

end Hoare

end Whiel

------------------------------------------------------------
-- The Two-Level Rule
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace Prophecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}
variable {assigned : Finset A}

/- Two levels: `I₀` at level `0`, `I₁` at level `1`. -/
def twoLevels
    (I₀ I₁ : List (Assertion D Ω)) :
    Nat → List (Assertion D Ω)
| 0 => I₀
| 1 => I₁
| _ + 2 => []

/- `Ω(I₀)` is the terminal-facts set below level `1`. -/
theorem prophecyBelow_one_iff
    (hExt : Ω.extensionOf Γ)
    (gc : ProphecyCollapse (D := D) hExt assigned)
    (G : Guard D Γ)
    (I₀ I₁ : List (Assertion D Ω))
    (J : Instance D Ω) :
    prophecyBelow gc G (twoLevels I₀ I₁) 1 J ↔
      prophecyOf gc G I₀ J := by
  unfold prophecyBelow prophecyOf
  constructor
  · intro h
    refine ⟨h.1 Nat.zero_lt_one, ?_⟩
    intro c hc
    exact h.2 0 Nat.zero_lt_one c hc
  · intro h
    refine ⟨fun _ => h.1, ?_⟩
    intro i hi c hc
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst hi0
    exact h.2 c hc

/-
  Rule 3.2 of the note, semantically. Level-`0` clauses get
  the ordinary obligations; level-`1` clauses and the
  postcondition get the obligations with `Ω(I₀)`.
-/
theorem hoareValid_while_of_two_level_vcs
    (hExt : Ω.extensionOf Γ)
    {G : Guard D Γ}
    {B : Cmd D Γ}
    (gc : ProphecyCollapse (D := D) hExt B.assignedSymbols)
    (I₀ I₁ : List (Assertion D Ω))
    {pre post : Assertion D Γ}
    (hInit₀ :
      ∀ c ∈ I₀, ∀ J : Instance D Ω,
        pre (Instance.reduct hExt J) → c J)
    (hStep₀ :
      ∀ c ∈ I₀, ∀ J : Instance D Ω,
        (∀ c' ∈ I₀, c' J) →
          (G.onExtension hExt).eval J →
            wp (B.onExtension hExt) c J)
    (hInit₁ :
      ∀ c ∈ I₁, ∀ J : Instance D Ω,
        pre (Instance.reduct hExt J) →
          prophecyOf gc G I₀ J → c J)
    (hStep₁ :
      ∀ c ∈ I₁, ∀ J : Instance D Ω,
        (∀ c' ∈ I₀, c' J) →
          (∀ c' ∈ I₁, c' J) →
            (G.onExtension hExt).eval J →
              prophecyOf gc G I₀ J →
                wp (B.onExtension hExt) c J)
    (hTerm :
      ∀ J : Instance D Ω,
        gc.collapse J = J →
          ¬ (G.onExtension hExt).eval J →
            (∀ c ∈ I₀, c J) →
              (∀ c ∈ I₁, c J) →
                post (Instance.reduct hExt J)) :
    HoareValid pre (.while G B) post := by
  apply hoareValid_while_of_leveled_vcs hExt gc
    (twoLevels I₀ I₁)
  · intro j c hc J hPre hOm
    match j, hc with
    | 0, hc =>
        exact hInit₀ c hc J hPre
    | 1, hc =>
        exact hInit₁ c hc J hPre
          ((prophecyBelow_one_iff hExt gc G I₀ I₁ J).mp
            hOm)
    | j + 2, hc =>
        exact absurd hc (List.not_mem_nil)
  · intro j c hc J hInv hG hOm
    match j, hc with
    | 0, hc =>
        exact hStep₀ c hc J (hInv 0 hOm) hG
    | 1, hc =>
        have hOm0 :
            prophecyBelow gc G (twoLevels I₀ I₁) 0 J :=
          prophecyBelow_mono gc G (twoLevels I₀ I₁)
            (Nat.zero_le 1) hOm
        exact hStep₁ c hc J (hInv 0 hOm0) (hInv 1 hOm) hG
          ((prophecyBelow_one_iff hExt gc G I₀ I₁ J).mp
            hOm)
    | j + 2, hc =>
        exact absurd hc (List.not_mem_nil)
  · intro J hFix hNotG hAll
    exact hTerm J hFix hNotG (hAll 0) (hAll 1)

end Prophecy

end Hoare

end Whiel
