-- Author: Jesse Comer
import Whiel.Preprocess.Equiv

/-
  The sequence merge of two framed loops.

  Two sequenced framed loops become one, in four cases
  selected by Booleans computed from the *source* terms and
  handed in: a loop-free first source goes into the prefix,
  a loop-free second source into the suffix, independent
  sources take the flag-free product, and otherwise two
  fresh flags run a two-phase program counter.

  Key definitions include:
    * `Whiel.Preprocess.Independent`
    * `Whiel.Preprocess.independentCheck`
    * `Whiel.Preprocess.mergeIntoPrefix`
    * `Whiel.Preprocess.mergeIntoSuffix`
    * `Whiel.Preprocess.mergeProduct`
    * `Whiel.Preprocess.mergeGeneral`
    * `Whiel.Preprocess.mergeSeq`

  Correctness is proven by:
    * `Whiel.Preprocess.mergeProduct_bigStepEquiv`
    * `Whiel.Preprocess.mergeGeneral_equivMod`
    * `Whiel.Preprocess.mergeSeq_equivMod`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Symbol Lists
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Relation names of a raw expression, as a list. -/
def rawSymbolList : RawRAExpr A D → List A
| .top => []
| .empty _ => []
| .rel X => [X]
| .single _ => []
| .select _ e => rawSymbolList e
| .proj _ e => rawSymbolList e
| .prod e₁ e₂ => rawSymbolList e₁ ++ rawSymbolList e₂
| .union e₁ e₂ => rawSymbolList e₁ ++ rawSymbolList e₂
| .diff e₁ e₂ => rawSymbolList e₁ ++ rawSymbolList e₂

@[simp] theorem mem_rawSymbolList_iff
    (X : A)
    (e : RawRAExpr A D) :
    X ∈ rawSymbolList e ↔ X ∈ e.symbols := by
  induction e with
  | top => simp [rawSymbolList, RawRAExpr.symbols]
  | empty n => simp [rawSymbolList, RawRAExpr.symbols]
  | rel Y => simp [rawSymbolList, RawRAExpr.symbols]
  | single d => simp [rawSymbolList, RawRAExpr.symbols]
  | select φ e ih =>
      simp [rawSymbolList, RawRAExpr.symbols, ih]
  | proj idxs e ih =>
      simp [rawSymbolList, RawRAExpr.symbols, ih]
  | prod e₁ e₂ ih₁ ih₂ =>
      simp [rawSymbolList, RawRAExpr.symbols, ih₁, ih₂]
  | union e₁ e₂ ih₁ ih₂ =>
      simp [rawSymbolList, RawRAExpr.symbols, ih₁, ih₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp [rawSymbolList, RawRAExpr.symbols, ih₁, ih₂]

/- Relation names of a guard, as a list. -/
def guardSymbolList : Guard D Γ → List A
| .«true» => []
| .«false» => []
| .eq e₁ e₂ =>
    rawSymbolList e₁.expr ++ rawSymbolList e₂.expr
| .subset e₁ e₂ =>
    rawSymbolList e₁.expr ++ rawSymbolList e₂.expr
| .and φ ψ => guardSymbolList φ ++ guardSymbolList ψ
| .or φ ψ => guardSymbolList φ ++ guardSymbolList ψ
| .not φ => guardSymbolList φ

@[simp] theorem mem_guardSymbolList_iff
    (X : A)
    (G : Guard D Γ) :
    X ∈ guardSymbolList G ↔ X ∈ G.symbols := by
  induction G with
  | «true» => simp [guardSymbolList, Guard.symbols]
  | «false» => simp [guardSymbolList, Guard.symbols]
  | eq e₁ e₂ =>
      simp [guardSymbolList, Guard.symbols,
        RAExpr.symbols]
  | subset e₁ e₂ =>
      simp [guardSymbolList, Guard.symbols,
        RAExpr.symbols]
  | and φ ψ ihφ ihψ =>
      simp [guardSymbolList, Guard.symbols, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [guardSymbolList, Guard.symbols, ihφ, ihψ]
  | not φ ih =>
      simp [guardSymbolList, Guard.symbols, ih]

/- Relation names assigned by a command, as a list. -/
def assignedList : Cmd D Γ → List A
| .skip => []
| .assign X _ => [X.1]
| .seq C₁ C₂ => assignedList C₁ ++ assignedList C₂
| .ite _ C₁ C₂ => assignedList C₁ ++ assignedList C₂
| .«while» _ C => assignedList C

@[simp] theorem mem_assignedList_iff
    (X : A)
    (C : Cmd D Γ) :
    X ∈ assignedList C ↔ X ∈ C.assignedSymbols := by
  induction C with
  | skip => simp [assignedList, Cmd.assignedSymbols]
  | assign Y e =>
      simp [assignedList, Cmd.assignedSymbols]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [assignedList, Cmd.assignedSymbols, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [assignedList, Cmd.assignedSymbols, ih₁, ih₂]
  | «while» G C ih =>
      simp [assignedList, Cmd.assignedSymbols, ih]

/- Relation names read or assigned, as a list. -/
def symbolList : Cmd D Γ → List A
| .skip => []
| .assign X e => X.1 :: rawSymbolList e.expr
| .seq C₁ C₂ => symbolList C₁ ++ symbolList C₂
| .ite G C₁ C₂ =>
    guardSymbolList G ++ symbolList C₁ ++ symbolList C₂
| .«while» G C => guardSymbolList G ++ symbolList C

@[simp] theorem mem_symbolList_iff
    (X : A)
    (C : Cmd D Γ) :
    X ∈ symbolList C ↔ X ∈ C.symbols := by
  induction C with
  | skip => simp [symbolList, Cmd.symbols]
  | assign Y e =>
      simp [symbolList, Cmd.symbols, RAExpr.symbols]
  | seq C₁ C₂ ih₁ ih₂ =>
      simp [symbolList, Cmd.symbols, ih₁, ih₂]
  | ite G C₁ C₂ ih₁ ih₂ =>
      simp [symbolList, Cmd.symbols, ih₁, ih₂]
  | «while» G C ih =>
      simp [symbolList, Cmd.symbols, ih]

end Preprocess

end Whiel

------------------------------------------------------------
-- Independence
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Two commands are independent when their assigned sets are
  disjoint and neither reads what the other assigns.
-/
def Independent (C₁ C₂ : Cmd D Γ) : Prop :=
  (∀ X ∈ C₁.assignedSymbols, X ∉ C₂.symbols) ∧
    (∀ X ∈ C₂.assignedSymbols, X ∉ C₁.symbols)

theorem Independent.symm
    {C₁ C₂ : Cmd D Γ}
    (h : Independent C₁ C₂) :
    Independent C₂ C₁ :=
  ⟨h.2, h.1⟩

/- Disjointness of two name lists, by list membership. -/
def disjointNames (xs ys : List A) : Bool :=
  xs.all (fun x => decide (x ∉ ys))

/- The independence check, a list computation. -/
def independentCheck (C₁ C₂ : Cmd D Γ) : Bool :=
  disjointNames (assignedList C₁) (symbolList C₂) &&
    disjointNames (assignedList C₂) (symbolList C₁)

/- A positive check implies semantic independence. -/
theorem independent_of_check
    {C₁ C₂ : Cmd D Γ}
    (hCheck : independentCheck C₁ C₂ = true) :
    Independent C₁ C₂ := by
  rw [independentCheck, Bool.and_eq_true] at hCheck
  constructor
  · intro X hX
    have hAll := List.all_eq_true.mp hCheck.1
    have hMem : X ∈ assignedList C₁ :=
      (mem_assignedList_iff X C₁).mpr hX
    have hDec := hAll X hMem
    simp only [decide_eq_true_eq] at hDec
    intro hSym
    exact hDec ((mem_symbolList_iff X C₂).mpr hSym)
  · intro X hX
    have hAll := List.all_eq_true.mp hCheck.2
    have hMem : X ∈ assignedList C₂ :=
      (mem_assignedList_iff X C₂).mpr hX
    have hDec := hAll X hMem
    simp only [decide_eq_true_eq] at hDec
    intro hSym
    exact hDec ((mem_symbolList_iff X C₁).mpr hSym)

end Preprocess

end Whiel

------------------------------------------------------------
-- Frame Support
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A run that assigns nothing in `S` leaves every relation
  of `S` alone.
-/
theorem agreeOn_of_bigStep_of_disjoint
    {C : Cmd D Γ}
    {I J : Instance D Γ}
    {S : Finset A}
    (hStep : Cmd.BigStep C I J)
    (hDisj : ∀ X ∈ C.assignedSymbols, X ∉ S) :
    Instance.agreeOn S I J := by
  intro X hX
  exact
    (Cmd.BigStep.no_update_preservation hStep X
      (fun hMem => hDisj X.1 hMem hX)).symm

/-
  Independent commands commute: running them in either
  order gives the same final state.
-/
theorem bigStep_seq_comm
    {C₁ C₂ : Cmd D Γ}
    (hIndep : Independent C₁ C₂)
    (I J : Instance D Γ) :
    Cmd.BigStep (.seq C₁ C₂) I J →
      Cmd.BigStep (.seq C₂ C₁) I J := by
  intro hStep
  rcases (Cmd.bigStep_seq_iff C₁ C₂ I J).mp hStep with
    ⟨M, hOne, hTwo⟩
  have hAgreeTwo :
      Instance.agreeOn C₂.symbols I M :=
    agreeOn_of_bigStep_of_disjoint hOne hIndep.1
  rcases
    Cmd.BigStep.frame (S := C₂.symbols)
      (subset_rfl) (Instance.agreeOn_symm hAgreeTwo)
      hTwo with ⟨J₁, hJ₁, hAgreeJ₁⟩
  have hAgreeOne :
      Instance.agreeOn C₁.symbols I J₁ :=
    agreeOn_of_bigStep_of_disjoint hJ₁ hIndep.2
  rcases
    Cmd.BigStep.frame (S := C₁.symbols)
      (subset_rfl) hAgreeOne hOne with
    ⟨J₂, hJ₂, hAgreeJ₂⟩
  have hEq : J₂ = J := by
    apply Instance.ext
    intro X
    by_cases hX₁ : X.1 ∈ C₁.symbols
    · have hLeft : M X = J₂ X := hAgreeJ₂ X hX₁
      have hRight : M X = J X := by
        refine
          (Cmd.BigStep.no_update_preservation hTwo X
            ?_).symm
        intro hMem
        exact hIndep.2 X.1 hMem hX₁
      rw [← hLeft, hRight]
    · have hOut : J₂ X = J₁ X := by
        refine
          Cmd.BigStep.no_update_preservation hJ₂ X ?_
        intro hMem
        exact hX₁
          (Cmd.assignedSymbols_subset_symbols _ hMem)
      by_cases hX₂ : X.1 ∈ C₂.symbols
      · have hJ : J X = J₁ X := hAgreeJ₁ X hX₂
        rw [hOut, hJ]
      · have hJ₁I : J₁ X = I X := by
          refine
            (Cmd.BigStep.no_update_preservation hJ₁ X
              ?_)
          intro hMem
          exact hX₂
            (Cmd.assignedSymbols_subset_symbols _ hMem)
        have hMI : M X = I X := by
          refine
            (Cmd.BigStep.no_update_preservation hOne X
              ?_)
          intro hMem
          exact hX₁
            (Cmd.assignedSymbols_subset_symbols _ hMem)
        have hJM : J X = M X := by
          refine
            (Cmd.BigStep.no_update_preservation hTwo X
              ?_)
          intro hMem
          exact hX₂
            (Cmd.assignedSymbols_subset_symbols _ hMem)
        rw [hOut, hJ₁I, hJM, hMI]
  rw [← hEq]
  exact Cmd.BigStep.seq hJ₁ hJ₂

/- Independent commands commute in either direction. -/
theorem bigStep_seq_comm_iff
    {C₁ C₂ : Cmd D Γ}
    (hIndep : Independent C₁ C₂)
    (I J : Instance D Γ) :
    Cmd.BigStep (.seq C₁ C₂) I J ↔
      Cmd.BigStep (.seq C₂ C₁) I J :=
  ⟨bigStep_seq_comm hIndep I J,
    bigStep_seq_comm hIndep.symm I J⟩

end Preprocess

end Whiel

------------------------------------------------------------
-- The Merge Operations
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/- The guarded product body of two loops. -/
def productBody
    (G₁ G₂ : Guard D Δ)
    (B₁ B₂ : Cmd D Δ) :
    Cmd D Δ :=
  .seq (.ite G₁ B₁ .skip) (.ite G₂ B₂ .skip)

/- The product loop of two loops. -/
def productLoop
    (G₁ G₂ : Guard D Δ)
    (B₁ B₂ : Cmd D Δ) :
    Cmd D Δ :=
  .«while» (.or G₁ G₂) (productBody G₁ G₂ B₁ B₂)

/-
  Merge case (i): loop-free code before a loop enters the
  prefix.
-/
def mergeIntoPrefix
    (L₁ L₂ : Framed D Δ) :
    Framed D Δ where
  init := .seq L₁.close L₂.init
  guard := L₂.guard
  body := L₂.body
  close := L₂.close

/-
  Merge case (ii): loop-free code after a loop enters the
  suffix.
-/
def mergeIntoSuffix
    (L₁ L₂ : Framed D Δ) :
    Framed D Δ where
  init := L₁.init
  guard := L₁.guard
  body := L₁.body
  close := .seq L₁.close L₂.close

/- The flag-free product of independent framed loops. -/
def mergeProduct
    (L₁ L₂ : Framed D Δ) :
    Framed D Δ where
  init := .seq L₁.init L₂.init
  guard := .or L₁.guard L₂.guard
  body :=
    productBody L₁.guard L₂.guard L₁.body L₂.body
  close := .seq L₁.close L₂.close

/-
  The phase switch of the general merge: lower the first
  flag, raise the second, and run the loop-free code
  between the two loops.
-/
def mergeSwitch
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    Cmd D Ω :=
  .seq f₁.lower
    (.seq f₂.raise
      (.seq (retag hExt L₁.close)
        (retag hExt L₂.init)))

/- The body of the general sequence merge. -/
def mergeGeneralBody
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    Cmd D Ω :=
  .ite f₁.test
    (.ite (L₁.guard.onExtension hExt)
      (retag hExt L₁.body)
      (mergeSwitch hExt f₁ f₂ L₁ L₂))
    (.ite (L₂.guard.onExtension hExt)
      (retag hExt L₂.body)
      f₂.lower)

/- The loop of the general sequence merge. -/
def mergeGeneralLoop
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    Cmd D Ω :=
  .«while» (.or f₁.test f₂.test)
    (mergeGeneralBody hExt f₁ f₂ L₁ L₂)

/-
  The second phase read on the source schema: the first
  loop, the code between the loops, and the second loop.
-/
def mergeTail
    (L₁ L₂ : Framed D Δ) :
    Cmd D Δ :=
  .seq (.«while» L₁.guard L₁.body)
    (.seq L₁.close
      (.seq L₂.init (.«while» L₂.guard L₂.body)))

/-
  Merge case (iii): a two-phase program counter written in
  two fresh flags.
-/
def mergeGeneral
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    Framed D Ω where
  init :=
    .seq (retag hExt L₁.init)
      (.seq f₁.raise f₂.lower)
  guard := .or f₁.test f₂.test
  body := mergeGeneralBody hExt f₁ f₂ L₁ L₂
  close := retag hExt L₂.close

/-
  The sequence merge. The three Booleans are computed from
  the source sub-terms by the caller and are never read off
  the framed loops; the priority is loop-free side first,
  product second, general merge last.
-/
def mergeSeq
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (loopFreeFirst loopFreeSecond independent : Bool) :
    Framed D Ω :=
  if loopFreeFirst then
    (mergeIntoPrefix L₁ L₂).retagOn hExt
  else if loopFreeSecond then
    (mergeIntoSuffix L₁ L₂).retagOn hExt
  else if independent then
    (mergeProduct L₁ L₂).retagOn hExt
  else
    mergeGeneral hExt f₁ f₂ L₁ L₂

/- The flag-free cases do not mention the drawn flags. -/
theorem mergeSeq_eq_of_loopFreeFirst
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (b c : Bool) :
    mergeSeq hExt f₁ f₂ L₁ L₂ true b c =
      (mergeIntoPrefix L₁ L₂).retagOn hExt :=
  rfl

theorem mergeSeq_eq_of_loopFreeSecond
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (c : Bool) :
    mergeSeq hExt f₁ f₂ L₁ L₂ false true c =
      (mergeIntoSuffix L₁ L₂).retagOn hExt :=
  rfl

theorem mergeSeq_eq_of_independent
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    mergeSeq hExt f₁ f₂ L₁ L₂ false false true =
      (mergeProduct L₁ L₂).retagOn hExt :=
  rfl

theorem mergeSeq_eq_general
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ) :
    mergeSeq hExt f₁ f₂ L₁ L₂ false false false =
      mergeGeneral hExt f₁ f₂ L₁ L₂ :=
  rfl

end Preprocess

end Whiel

------------------------------------------------------------
-- The Loop-Free Sides
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ : UnnamedSchema A}

/- Merge case (i) on a base first side. -/
theorem mergeIntoPrefix_base_bigStepEquiv
    (C : Cmd D Δ)
    (L₂ : Framed D Δ) :
    Cmd.BigStepEquiv
      (.seq (Framed.base C).unfold L₂.unfold)
      (mergeIntoPrefix (Framed.base C) L₂).unfold := by
  intro I J
  rw [Cmd.bigStep_seq_iff]
  constructor
  · rintro ⟨K, hOne, hTwo⟩
    rw [Framed.bigStep_base_iff] at hOne
    rw [Framed.bigStep_unfold_iff] at hTwo
    obtain ⟨K₁, K₂, hInit, hLoop, hClose⟩ := hTwo
    rw [Framed.bigStep_unfold_iff]
    exact
      ⟨K₁, K₂, Cmd.BigStep.seq hOne hInit,
        hLoop, hClose⟩
  · intro hStep
    rw [Framed.bigStep_unfold_iff] at hStep
    obtain ⟨K₁, K₂, hInit, hLoop, hClose⟩ := hStep
    rcases
      (Cmd.bigStep_seq_iff C L₂.init I K₁).mp hInit with
      ⟨K, hOne, hTwo⟩
    refine ⟨K, ?_, ?_⟩
    · rw [Framed.bigStep_base_iff]
      exact hOne
    · rw [Framed.bigStep_unfold_iff]
      exact ⟨K₁, K₂, hTwo, hLoop, hClose⟩

/- Merge case (i) is correct when the first side is base. -/
theorem mergeIntoPrefix_bigStepEquiv
    {L₁ L₂ : Framed D Δ}
    (hBase : L₁.IsBase) :
    Cmd.BigStepEquiv
      (.seq L₁.unfold L₂.unfold)
      (mergeIntoPrefix L₁ L₂).unfold := by
  have hEquiv :=
    mergeIntoPrefix_base_bigStepEquiv L₁.close L₂
  rw [← Framed.eq_base_of_isBase hBase] at hEquiv
  exact hEquiv

/- Merge case (ii) on a base second side. -/
theorem mergeIntoSuffix_base_bigStepEquiv
    (L₁ : Framed D Δ)
    (C : Cmd D Δ) :
    Cmd.BigStepEquiv
      (.seq L₁.unfold (Framed.base C).unfold)
      (mergeIntoSuffix L₁ (Framed.base C)).unfold := by
  intro I J
  rw [Cmd.bigStep_seq_iff]
  constructor
  · rintro ⟨K, hOne, hTwo⟩
    rw [Framed.bigStep_base_iff] at hTwo
    rw [Framed.bigStep_unfold_iff] at hOne
    obtain ⟨K₁, K₂, hInit, hLoop, hClose⟩ := hOne
    rw [Framed.bigStep_unfold_iff]
    exact
      ⟨K₁, K₂, hInit, hLoop,
        Cmd.BigStep.seq hClose hTwo⟩
  · intro hStep
    rw [Framed.bigStep_unfold_iff] at hStep
    obtain ⟨K₁, K₂, hInit, hLoop, hClose⟩ := hStep
    rcases
      (Cmd.bigStep_seq_iff L₁.close C K₂ J).mp
        hClose with ⟨K, hOne, hTwo⟩
    refine ⟨K, ?_, ?_⟩
    · rw [Framed.bigStep_unfold_iff]
      exact ⟨K₁, K₂, hInit, hLoop, hOne⟩
    · rw [Framed.bigStep_base_iff]
      exact hTwo

/- Merge case (ii) is correct when the second side is
  base. -/
theorem mergeIntoSuffix_bigStepEquiv
    {L₁ L₂ : Framed D Δ}
    (hBase : L₂.IsBase) :
    Cmd.BigStepEquiv
      (.seq L₁.unfold L₂.unfold)
      (mergeIntoSuffix L₁ L₂).unfold := by
  have hEquiv :=
    mergeIntoSuffix_base_bigStepEquiv L₁ L₂.close
  rw [← Framed.eq_base_of_isBase hBase] at hEquiv
  exact hEquiv

end Preprocess

end Whiel

------------------------------------------------------------
-- Agreement And Footprint Support
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ : UnnamedSchema A}

theorem agreeOn_refl
    (S : Finset A)
    (I : Instance D Δ) :
    Instance.agreeOn S I I :=
  fun _ _ => rfl

theorem agreeOn_trans
    {S : Finset A}
    {I J K : Instance D Δ}
    (h₁ : Instance.agreeOn S I J)
    (h₂ : Instance.agreeOn S J K) :
    Instance.agreeOn S I K := by
  intro X hX
  exact (h₁ X hX).trans (h₂ X hX)

/- Independence is monotone in both footprints. -/
theorem Independent.mono
    {C₁ C₂ C₁' C₂' : Cmd D Δ}
    (hIndep : Independent C₁ C₂)
    (hAsgOne :
      C₁'.assignedSymbols ⊆ C₁.assignedSymbols)
    (hSymOne : C₁'.symbols ⊆ C₁.symbols)
    (hAsgTwo :
      C₂'.assignedSymbols ⊆ C₂.assignedSymbols)
    (hSymTwo : C₂'.symbols ⊆ C₂.symbols) :
    Independent C₁' C₂' := by
  constructor
  · intro X hX hMem
    exact hIndep.1 X (hAsgOne hX) (hSymTwo hMem)
  · intro X hX hMem
    exact hIndep.2 X (hAsgTwo hX) (hSymOne hMem)

@[simp] theorem mem_unfold_assignedSymbols_iff
    (L : Framed D Δ)
    (X : A) :
    X ∈ L.unfold.assignedSymbols ↔
      X ∈ L.init.assignedSymbols ∨
        X ∈ L.body.assignedSymbols ∨
          X ∈ L.close.assignedSymbols := by
  simp [Framed.unfold, Cmd.assignedSymbols]

@[simp] theorem mem_unfold_symbols_iff
    (L : Framed D Δ)
    (X : A) :
    X ∈ L.unfold.symbols ↔
      X ∈ L.init.symbols ∨
        X ∈ L.guard.symbols ∨
          X ∈ L.body.symbols ∨
            X ∈ L.close.symbols := by
  simp [Framed.unfold, Cmd.symbols]

theorem init_assignedSymbols_subset
    (L : Framed D Δ) :
    L.init.assignedSymbols ⊆
      L.unfold.assignedSymbols := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff]
  exact Or.inl hX

theorem init_symbols_subset
    (L : Framed D Δ) :
    L.init.symbols ⊆ L.unfold.symbols := by
  intro X hX
  simp only [mem_unfold_symbols_iff]
  exact Or.inl hX

theorem close_assignedSymbols_subset
    (L : Framed D Δ) :
    L.close.assignedSymbols ⊆
      L.unfold.assignedSymbols := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff]
  exact Or.inr (Or.inr hX)

theorem close_symbols_subset
    (L : Framed D Δ) :
    L.close.symbols ⊆ L.unfold.symbols := by
  intro X hX
  simp only [mem_unfold_symbols_iff]
  exact Or.inr (Or.inr (Or.inr hX))

theorem body_assignedSymbols_subset
    (L : Framed D Δ) :
    L.body.assignedSymbols ⊆
      L.unfold.assignedSymbols := by
  intro X hX
  simp only [mem_unfold_assignedSymbols_iff]
  exact Or.inr (Or.inl hX)

theorem body_symbols_subset
    (L : Framed D Δ) :
    L.body.symbols ⊆ L.unfold.symbols := by
  intro X hX
  simp only [mem_unfold_symbols_iff]
  exact Or.inr (Or.inr (Or.inl hX))

theorem guard_symbols_subset
    (L : Framed D Δ) :
    L.guard.symbols ⊆ L.unfold.symbols := by
  intro X hX
  simp only [mem_unfold_symbols_iff]
  exact Or.inr (Or.inl hX)

theorem loop_assignedSymbols_subset
    (L : Framed D Δ) :
    (Cmd.«while» L.guard L.body).assignedSymbols ⊆
      L.unfold.assignedSymbols :=
  body_assignedSymbols_subset L

theorem loop_symbols_subset
    (L : Framed D Δ) :
    (Cmd.«while» L.guard L.body).symbols ⊆
      L.unfold.symbols := by
  intro X hX
  simp only [Cmd.symbols, Finset.mem_union] at hX
  simp only [mem_unfold_symbols_iff]
  rcases hX with hGuard | hBody
  · exact Or.inr (Or.inl hGuard)
  · exact Or.inr (Or.inr (Or.inl hBody))

end Preprocess

end Whiel

------------------------------------------------------------
-- The Product Loop
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ : UnnamedSchema A}

private theorem ite_assigned_not_mem
    {G : Guard D Δ}
    {B : Cmd D Δ}
    {S : Finset A}
    (hA : ∀ X ∈ B.assignedSymbols, X ∉ S) :
    ∀ X ∈ (Cmd.ite G B (.skip : Cmd D Δ)).assignedSymbols,
      X ∉ S := by
  intro X hX
  simp only [Cmd.assignedSymbols, Finset.mem_union,
    Finset.notMem_empty, or_false] at hX
  exact hA X hX

/- The product loop projects to a run of the first loop. -/
theorem productLoop_project_left
    {G₁ G₂ : Guard D Δ}
    {B₁ B₂ : Cmd D Δ}
    {S₁ : Finset A}
    (hGuard : G₁.symbols ⊆ S₁)
    (hBody : B₁.symbols ⊆ S₁)
    (hOther : ∀ X ∈ B₂.assignedSymbols, X ∉ S₁)
    {I J : Instance D Δ}
    (hStep :
      Cmd.BigStep (productLoop G₁ G₂ B₁ B₂) I J) :
    ∀ I₁ : Instance D Δ,
      Instance.agreeOn S₁ I I₁ →
        ∃ K : Instance D Δ,
          Cmd.BigStep (.«while» G₁ B₁) I₁ K ∧
            Instance.agreeOn S₁ J K := by
  unfold productLoop at hStep
  generalize hW :
      (Cmd.«while» (Guard.or G₁ G₂)
        (productBody G₁ G₂ B₁ B₂) : Cmd D Δ) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G C I hFalse =>
      cases hW
      intro I₁ hAgree
      refine ⟨I₁, ?_, hAgree⟩
      refine Cmd.BigStep.while_false ?_
      intro hEval
      exact hFalse
        (Or.inl
          ((Guard.eval_reduct_property G₁
            (Instance.agreeOn_of_subset hGuard
              hAgree)).mpr hEval))
  | @while_true G C I M J hEval hRun hLoop ihRun ihLoop =>
      cases hW
      intro I₁ hAgree
      rcases
        (Cmd.bigStep_seq_iff _ _ I M).mp hRun with
        ⟨N, hFirst, hSecond⟩
      have hAgreeNM : Instance.agreeOn S₁ N M :=
        agreeOn_of_bigStep_of_disjoint hSecond
          (ite_assigned_not_mem hOther)
      rcases (Cmd.bigStep_ite_iff _ _ _ I N).mp hFirst
        with hTrue | hFalse
      · have hG₁ : G₁.eval I₁ :=
          (Guard.eval_reduct_property G₁
            (Instance.agreeOn_of_subset hGuard
              hAgree)).mp hTrue.1
        rcases
          Cmd.BigStep.frame (S := S₁) hBody hAgree
            hTrue.2 with ⟨N₁, hRunN, hAgreeN⟩
        rcases
          ihLoop rfl N₁
            (agreeOn_trans
              (Instance.agreeOn_symm hAgreeNM)
              hAgreeN) with ⟨K, hK, hAgreeK⟩
        exact
          ⟨K, Cmd.BigStep.while_true hG₁ hRunN hK,
            hAgreeK⟩
      · have hNI : N = I :=
          (Cmd.bigStep_skip_iff I N).mp hFalse.2
        subst hNI
        exact
          ihLoop rfl I₁
            (agreeOn_trans
              (Instance.agreeOn_symm hAgreeNM) hAgree)

/- The product loop projects to a run of the second loop. -/
theorem productLoop_project_right
    {G₁ G₂ : Guard D Δ}
    {B₁ B₂ : Cmd D Δ}
    {S₂ : Finset A}
    (hGuard : G₂.symbols ⊆ S₂)
    (hBody : B₂.symbols ⊆ S₂)
    (hOther : ∀ X ∈ B₁.assignedSymbols, X ∉ S₂)
    {I J : Instance D Δ}
    (hStep :
      Cmd.BigStep (productLoop G₁ G₂ B₁ B₂) I J) :
    ∀ I₂ : Instance D Δ,
      Instance.agreeOn S₂ I I₂ →
        ∃ K : Instance D Δ,
          Cmd.BigStep (.«while» G₂ B₂) I₂ K ∧
            Instance.agreeOn S₂ J K := by
  unfold productLoop at hStep
  generalize hW :
      (Cmd.«while» (Guard.or G₁ G₂)
        (productBody G₁ G₂ B₁ B₂) : Cmd D Δ) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G C I hFalse =>
      cases hW
      intro I₂ hAgree
      refine ⟨I₂, ?_, hAgree⟩
      refine Cmd.BigStep.while_false ?_
      intro hEval
      exact hFalse
        (Or.inr
          ((Guard.eval_reduct_property G₂
            (Instance.agreeOn_of_subset hGuard
              hAgree)).mpr hEval))
  | @while_true G C I M J hEval hRun hLoop ihRun ihLoop =>
      cases hW
      intro I₂ hAgree
      rcases
        (Cmd.bigStep_seq_iff _ _ I M).mp hRun with
        ⟨N, hFirst, hSecond⟩
      have hAgreeIN : Instance.agreeOn S₂ I N :=
        agreeOn_of_bigStep_of_disjoint hFirst
          (ite_assigned_not_mem hOther)
      have hAgreeNI : Instance.agreeOn S₂ N I₂ :=
        agreeOn_trans (Instance.agreeOn_symm hAgreeIN)
          hAgree
      rcases (Cmd.bigStep_ite_iff _ _ _ N M).mp hSecond
        with hTrue | hFalse
      · have hG₂ : G₂.eval I₂ :=
          (Guard.eval_reduct_property G₂
            (Instance.agreeOn_of_subset hGuard
              hAgreeNI)).mp hTrue.1
        rcases
          Cmd.BigStep.frame (S := S₂) hBody hAgreeNI
            hTrue.2 with ⟨M₂, hRunM, hAgreeM⟩
        rcases ihLoop rfl M₂ hAgreeM with
          ⟨K, hK, hAgreeK⟩
        exact
          ⟨K, Cmd.BigStep.while_true hG₂ hRunM hK,
            hAgreeK⟩
      · have hMN : M = N :=
          (Cmd.bigStep_skip_iff N M).mp hFalse.2
        subst hMN
        exact ihLoop rfl I₂ hAgreeNI

/-
  With the first guard false and staying false, the product
  loop runs the second loop alone.
-/
theorem productLoop_terminates_right
    {G₁ G₂ : Guard D Δ}
    {B₁ B₂ : Cmd D Δ}
    {S₁ S₂ : Finset A}
    (hGuardOne : G₁.symbols ⊆ S₁)
    (hGuardTwo : G₂.symbols ⊆ S₂)
    (hBodyTwo : B₂.symbols ⊆ S₂)
    (hOtherTwo : ∀ X ∈ B₂.assignedSymbols, X ∉ S₁)
    {I₂ M : Instance D Δ}
    (hStep : Cmd.BigStep (.«while» G₂ B₂) I₂ M) :
    ∀ I : Instance D Δ,
      ¬ G₁.eval I →
      Instance.agreeOn S₂ I₂ I →
        ∃ J : Instance D Δ,
          Cmd.BigStep (productLoop G₁ G₂ B₁ B₂) I J := by
  generalize hW :
      (Cmd.«while» G₂ B₂ : Cmd D Δ) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G C I hFalse =>
      cases hW
      intro I hnG₁ hAgree
      refine ⟨I, Cmd.BigStep.while_false ?_⟩
      rintro (hOne | hTwo)
      · exact hnG₁ hOne
      · exact hFalse
          ((Guard.eval_reduct_property G₂
            (Instance.agreeOn_of_subset hGuardTwo
              hAgree)).mpr hTwo)
  | @while_true G C I₂ M₂ M hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      intro I hnG₁ hAgree
      have hG₂ : G₂.eval I :=
        (Guard.eval_reduct_property G₂
          (Instance.agreeOn_of_subset hGuardTwo
            hAgree)).mp hEval
      rcases
        Cmd.BigStep.frame (S := S₂) hBodyTwo hAgree
          hRun with ⟨N, hRunN, hAgreeN⟩
      have hAgreeIN : Instance.agreeOn S₁ I N :=
        agreeOn_of_bigStep_of_disjoint hRunN hOtherTwo
      have hnG₁N : ¬ G₁.eval N := by
        intro hEvalN
        exact hnG₁
          ((Guard.eval_reduct_property G₁
            (Instance.agreeOn_of_subset hGuardOne
              hAgreeIN)).mpr hEvalN)
      rcases ihLoop rfl N hnG₁N hAgreeN with ⟨J, hJ⟩
      refine
        ⟨J, Cmd.BigStep.while_true (Or.inr hG₂) ?_ hJ⟩
      refine Cmd.BigStep.seq (I₁ := I) ?_ ?_
      · exact Cmd.BigStep.ite_false hnG₁
          (Cmd.BigStep.skip I)
      · exact Cmd.BigStep.ite_true hG₂ hRunN

/- The product loop terminates when both loops do. -/
theorem productLoop_terminates
    {G₁ G₂ : Guard D Δ}
    {B₁ B₂ : Cmd D Δ}
    {S₁ S₂ : Finset A}
    (hGuardOne : G₁.symbols ⊆ S₁)
    (hBodyOne : B₁.symbols ⊆ S₁)
    (hGuardTwo : G₂.symbols ⊆ S₂)
    (hBodyTwo : B₂.symbols ⊆ S₂)
    (hOtherOne : ∀ X ∈ B₁.assignedSymbols, X ∉ S₂)
    (hOtherTwo : ∀ X ∈ B₂.assignedSymbols, X ∉ S₁)
    {I₁ K : Instance D Δ}
    (hStep : Cmd.BigStep (.«while» G₁ B₁) I₁ K) :
    ∀ I₂ M : Instance D Δ,
      Cmd.BigStep (.«while» G₂ B₂) I₂ M →
        ∀ I : Instance D Δ,
          Instance.agreeOn S₁ I₁ I →
          Instance.agreeOn S₂ I₂ I →
            ∃ J : Instance D Δ,
              Cmd.BigStep
                (productLoop G₁ G₂ B₁ B₂) I J := by
  generalize hW :
      (Cmd.«while» G₁ B₁ : Cmd D Δ) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G C I₁ hFalse =>
      cases hW
      intro I₂ M hTwo I hAgreeOne hAgreeTwo
      have hnG₁ : ¬ G₁.eval I := by
        intro hEval
        exact hFalse
          ((Guard.eval_reduct_property G₁
            (Instance.agreeOn_of_subset hGuardOne
              hAgreeOne)).mpr hEval)
      exact
        productLoop_terminates_right (B₁ := B₁)
          hGuardOne hGuardTwo hBodyTwo hOtherTwo hTwo I
          hnG₁ hAgreeTwo
  | @while_true G C I₁ N₁ K hEval hRun hLoop ihRun
      ihLoop =>
      cases hW
      intro I₂ M hTwo I hAgreeOne hAgreeTwo
      have hG₁ : G₁.eval I :=
        (Guard.eval_reduct_property G₁
          (Instance.agreeOn_of_subset hGuardOne
            hAgreeOne)).mp hEval
      rcases
        Cmd.BigStep.frame (S := S₁) hBodyOne hAgreeOne
          hRun with ⟨N, hRunN, hAgreeN⟩
      have hAgreeIN : Instance.agreeOn S₂ I N :=
        agreeOn_of_bigStep_of_disjoint hRunN hOtherOne
      have hAgreeTwoN : Instance.agreeOn S₂ I₂ N :=
        agreeOn_trans hAgreeTwo hAgreeIN
      by_cases hG₂N : G₂.eval N
      · have hG₂ : G₂.eval I₂ :=
          (Guard.eval_reduct_property G₂
            (Instance.agreeOn_of_subset hGuardTwo
              hAgreeTwoN)).mpr hG₂N
        rcases
          (Cmd.bigStep_while_iff G₂ B₂ I₂ M).mp hTwo with
          hStop | ⟨M₂, _, hRunTwo, hLoopTwo⟩
        · exact absurd hG₂ hStop.1
        · rcases
            Cmd.BigStep.frame (S := S₂) hBodyTwo
              hAgreeTwoN hRunTwo with
            ⟨N', hRunN', hAgreeN'⟩
          have hAgreeNN' : Instance.agreeOn S₁ N N' :=
            agreeOn_of_bigStep_of_disjoint hRunN'
              hOtherTwo
          rcases
            ihLoop rfl M₂ M hLoopTwo N'
              (agreeOn_trans hAgreeN hAgreeNN')
              hAgreeN' with ⟨J, hJ⟩
          refine
            ⟨J,
              Cmd.BigStep.while_true (Or.inl hG₁) ?_ hJ⟩
          refine Cmd.BigStep.seq (I₁ := N) ?_ ?_
          · exact Cmd.BigStep.ite_true hG₁ hRunN
          · exact Cmd.BigStep.ite_true hG₂N hRunN'
      · rcases
          ihLoop rfl I₂ M hTwo N hAgreeN hAgreeTwoN with
          ⟨J, hJ⟩
        refine
          ⟨J, Cmd.BigStep.while_true (Or.inl hG₁) ?_ hJ⟩
        refine Cmd.BigStep.seq (I₁ := N) ?_ ?_
        · exact Cmd.BigStep.ite_true hG₁ hRunN
        · exact Cmd.BigStep.ite_false hG₂N
            (Cmd.BigStep.skip N)

/- The product run and the sequential run end together. -/
private theorem productLoop_state_eq
    {G₁ G₂ : Guard D Δ}
    {B₁ B₂ : Cmd D Δ}
    {S₁ S₂ : Finset A}
    (hBodyOne : B₁.symbols ⊆ S₁)
    (hBodyTwo : B₂.symbols ⊆ S₂)
    (hOtherTwo : ∀ X ∈ B₂.assignedSymbols, X ∉ S₁)
    {I J K M : Instance D Δ}
    (hOne : Cmd.BigStep (.«while» G₁ B₁) I K)
    (hTwo : Cmd.BigStep (.«while» G₂ B₂) K M)
    (hProd : Cmd.BigStep (productLoop G₁ G₂ B₁ B₂) I J)
    (hAgreeOne : Instance.agreeOn S₁ J K)
    (hAgreeTwo : Instance.agreeOn S₂ J M) :
    J = M := by
  apply Instance.ext
  intro X
  by_cases hX₂ : X.1 ∈ S₂
  · exact hAgreeTwo X hX₂
  · by_cases hX₁ : X.1 ∈ S₁
    · have hMK : M X = K X := by
        refine
          Cmd.BigStep.no_update_preservation hTwo X ?_
        intro hMem
        exact hOtherTwo X.1 hMem hX₁
      rw [hAgreeOne X hX₁, hMK]
    · have hJI : J X = I X := by
        refine
          Cmd.BigStep.no_update_preservation hProd X ?_
        intro hMem
        simp only [productLoop, productBody,
          Cmd.assignedSymbols, Finset.mem_union,
          Finset.notMem_empty, or_false] at hMem
        rcases hMem with hOne' | hTwo'
        · exact hX₁
            (hBodyOne
              (Cmd.assignedSymbols_subset_symbols _
                hOne'))
        · exact hX₂
            (hBodyTwo
              (Cmd.assignedSymbols_subset_symbols _
                hTwo'))
      have hKI : K X = I X := by
        refine
          Cmd.BigStep.no_update_preservation hOne X ?_
        intro hMem
        exact hX₁
          (hBodyOne
            (Cmd.assignedSymbols_subset_symbols _ hMem))
      have hMK : M X = K X := by
        refine
          Cmd.BigStep.no_update_preservation hTwo X ?_
        intro hMem
        exact hX₂
          (hBodyTwo
            (Cmd.assignedSymbols_subset_symbols _ hMem))
      rw [hJI, hMK, hKI]

/- Two independent loops in sequence are their product. -/
theorem productLoop_bigStepEquiv
    {G₁ G₂ : Guard D Δ}
    {B₁ B₂ : Cmd D Δ}
    {S₁ S₂ : Finset A}
    (hGuardOne : G₁.symbols ⊆ S₁)
    (hBodyOne : B₁.symbols ⊆ S₁)
    (hGuardTwo : G₂.symbols ⊆ S₂)
    (hBodyTwo : B₂.symbols ⊆ S₂)
    (hOtherOne : ∀ X ∈ B₁.assignedSymbols, X ∉ S₂)
    (hOtherTwo : ∀ X ∈ B₂.assignedSymbols, X ∉ S₁) :
    Cmd.BigStepEquiv
      (.seq (.«while» G₁ B₁) (.«while» G₂ B₂))
      (productLoop G₁ G₂ B₁ B₂) := by
  intro I J
  constructor
  · intro hSeq
    rcases (Cmd.bigStep_seq_iff _ _ I J).mp hSeq with
      ⟨K, hOne, hTwo⟩
    have hAgreeIK : Instance.agreeOn S₂ I K :=
      agreeOn_of_bigStep_of_disjoint hOne hOtherOne
    rcases
      productLoop_terminates hGuardOne hBodyOne
        hGuardTwo hBodyTwo hOtherOne hOtherTwo hOne
        K J hTwo I (agreeOn_refl S₁ I)
        (Instance.agreeOn_symm hAgreeIK) with ⟨J', hProd⟩
    rcases
      productLoop_project_left hGuardOne hBodyOne
        hOtherTwo hProd I (agreeOn_refl S₁ I) with
      ⟨K', hK', hAgreeOne⟩
    have hKK : K' = K :=
      Cmd.BigStep.deterministic hK' hOne
    subst hKK
    rcases
      productLoop_project_right hGuardTwo hBodyTwo
        hOtherOne hProd K' hAgreeIK with
      ⟨M', hM', hAgreeTwo⟩
    have hMJ : M' = J :=
      Cmd.BigStep.deterministic hM' hTwo
    subst hMJ
    have hJJ : J' = M' :=
      productLoop_state_eq hBodyOne hBodyTwo hOtherTwo
        hOne hTwo hProd hAgreeOne hAgreeTwo
    rw [← hJJ]
    exact hProd
  · intro hProd
    rcases
      productLoop_project_left hGuardOne hBodyOne
        hOtherTwo hProd I (agreeOn_refl S₁ I) with
      ⟨K, hK, hAgreeOne⟩
    have hAgreeIK : Instance.agreeOn S₂ I K :=
      agreeOn_of_bigStep_of_disjoint hK hOtherOne
    rcases
      productLoop_project_right hGuardTwo hBodyTwo
        hOtherOne hProd K hAgreeIK with
      ⟨M, hM, hAgreeTwo⟩
    have hJM : J = M :=
      productLoop_state_eq hBodyOne hBodyTwo hOtherTwo
        hK hM hProd hAgreeOne hAgreeTwo
    rw [Cmd.bigStep_seq_iff]
    exact ⟨K, hK, by rw [hJM]; exact hM⟩

end Preprocess

end Whiel

------------------------------------------------------------
-- The Product Merge
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ : UnnamedSchema A}

theorem bigStepEquiv_seq_left
    {C₁ C₁' : Cmd D Δ}
    (h : Cmd.BigStepEquiv C₁ C₁')
    (C₂ : Cmd D Δ) :
    Cmd.BigStepEquiv (.seq C₁ C₂) (.seq C₁' C₂) := by
  intro I J
  rw [Cmd.bigStep_seq_iff, Cmd.bigStep_seq_iff]
  constructor
  · rintro ⟨K, h₁, h₂⟩
    exact ⟨K, (h I K).mp h₁, h₂⟩
  · rintro ⟨K, h₁, h₂⟩
    exact ⟨K, (h I K).mpr h₁, h₂⟩

theorem bigStepEquiv_seq_right
    (C₁ : Cmd D Δ)
    {C₂ C₂' : Cmd D Δ}
    (h : Cmd.BigStepEquiv C₂ C₂') :
    Cmd.BigStepEquiv (.seq C₁ C₂) (.seq C₁ C₂') := by
  intro I J
  rw [Cmd.bigStep_seq_iff, Cmd.bigStep_seq_iff]
  constructor
  · rintro ⟨K, h₁, h₂⟩
    exact ⟨K, h₁, (h K J).mp h₂⟩
  · rintro ⟨K, h₁, h₂⟩
    exact ⟨K, h₁, (h K J).mpr h₂⟩

theorem bigStepEquiv_seq_assoc
    (C₁ C₂ C₃ : Cmd D Δ) :
    Cmd.BigStepEquiv
      (.seq (.seq C₁ C₂) C₃)
      (.seq C₁ (.seq C₂ C₃)) := by
  intro I J
  simp only [Cmd.bigStep_seq_iff]
  constructor
  · rintro ⟨K, ⟨K', h₁, h₂⟩, h₃⟩
    exact ⟨K', h₁, K, h₂, h₃⟩
  · rintro ⟨K', h₁, K, h₂, h₃⟩
    exact ⟨K, ⟨K', h₁, h₂⟩, h₃⟩

theorem bigStepEquiv_seq_swap
    {C₁ C₂ : Cmd D Δ}
    (hIndep : Independent C₁ C₂)
    (C₃ : Cmd D Δ) :
    Cmd.BigStepEquiv
      (.seq C₁ (.seq C₂ C₃))
      (.seq C₂ (.seq C₁ C₃)) :=
  Cmd.BigStepEquiv.trans
    (Cmd.BigStepEquiv.trans
      (Cmd.BigStepEquiv.symm
        (bigStepEquiv_seq_assoc C₁ C₂ C₃))
      (bigStepEquiv_seq_left
        (fun I J => bigStep_seq_comm_iff hIndep I J) C₃))
    (bigStepEquiv_seq_assoc C₂ C₁ C₃)

/- The flag-free product of independent framed loops. -/
theorem mergeProduct_bigStepEquiv
    {L₁ L₂ : Framed D Δ}
    (hIndep : Independent L₁.unfold L₂.unfold) :
    Cmd.BigStepEquiv
      (.seq L₁.unfold L₂.unfold)
      (mergeProduct L₁ L₂).unfold := by
  have hCloseInit : Independent L₁.close L₂.init :=
    hIndep.mono (close_assignedSymbols_subset L₁)
      (close_symbols_subset L₁)
      (init_assignedSymbols_subset L₂)
      (init_symbols_subset L₂)
  have hLoopInit :
      Independent
        (.«while» L₁.guard L₁.body) L₂.init :=
    hIndep.mono (loop_assignedSymbols_subset L₁)
      (loop_symbols_subset L₁)
      (init_assignedSymbols_subset L₂)
      (init_symbols_subset L₂)
  have hCloseLoop :
      Independent L₁.close
        (.«while» L₂.guard L₂.body) :=
    hIndep.mono (close_assignedSymbols_subset L₁)
      (close_symbols_subset L₁)
      (loop_assignedSymbols_subset L₂)
      (loop_symbols_subset L₂)
  have hLoops :
      Cmd.BigStepEquiv
        (.seq (.«while» L₁.guard L₁.body)
          (.«while» L₂.guard L₂.body))
        (productLoop L₁.guard L₂.guard L₁.body
          L₂.body) :=
    productLoop_bigStepEquiv
      (S₁ := L₁.unfold.symbols)
      (S₂ := L₂.unfold.symbols)
      (guard_symbols_subset L₁) (body_symbols_subset L₁)
      (guard_symbols_subset L₂) (body_symbols_subset L₂)
      (fun X hX =>
        hIndep.1 X (body_assignedSymbols_subset L₁ hX))
      (fun X hX =>
        hIndep.2 X (body_assignedSymbols_subset L₂ hX))
  change Cmd.BigStepEquiv
    (.seq
      (.seq L₁.init
        (.seq (.«while» L₁.guard L₁.body) L₁.close))
      (.seq L₂.init
        (.seq (.«while» L₂.guard L₂.body) L₂.close)))
    (.seq (.seq L₁.init L₂.init)
      (.seq
        (productLoop L₁.guard L₂.guard L₁.body L₂.body)
        (.seq L₁.close L₂.close)))
  refine Cmd.BigStepEquiv.trans
    (bigStepEquiv_seq_assoc _ _ _) ?_
  refine Cmd.BigStepEquiv.trans
    (bigStepEquiv_seq_right _
      (bigStepEquiv_seq_assoc _ _ _)) ?_
  refine Cmd.BigStepEquiv.trans
    (bigStepEquiv_seq_right _
      (bigStepEquiv_seq_right _
        (bigStepEquiv_seq_swap hCloseInit _))) ?_
  refine Cmd.BigStepEquiv.trans
    (bigStepEquiv_seq_right _
      (bigStepEquiv_seq_swap hLoopInit _)) ?_
  refine Cmd.BigStepEquiv.trans
    (bigStepEquiv_seq_right _
      (bigStepEquiv_seq_right _
        (bigStepEquiv_seq_right _
          (bigStepEquiv_seq_swap hCloseLoop _)))) ?_
  refine Cmd.BigStepEquiv.trans
    (bigStepEquiv_seq_right _
      (bigStepEquiv_seq_right _
        (Cmd.BigStepEquiv.symm
          (bigStepEquiv_seq_assoc _ _ _)))) ?_
  refine Cmd.BigStepEquiv.trans
    (bigStepEquiv_seq_right _
      (bigStepEquiv_seq_right _
        (bigStepEquiv_seq_left hLoops _))) ?_
  exact Cmd.BigStepEquiv.symm
    (bigStepEquiv_seq_assoc _ _ _)

end Preprocess

end Whiel

------------------------------------------------------------
-- The General Merge
------------------------------------------------------------

namespace Whiel

namespace Preprocess

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Δ Ω : UnnamedSchema A}

/-
  Claims A and B of the merge lemma, read forwards: a run
  of the merged loop projects to a run of the phase it is
  in, and leaves both flags down.
-/
theorem mergeGeneral_project
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (hFresh₁ : f₁.sym.1 ∉ Δ.syms)
    (hFresh₂ : f₂.sym.1 ∉ Δ.syms)
    (hNe : f₁.sym ≠ f₂.sym)
    (L₁ L₂ : Framed D Δ)
    {u v : Instance D Ω}
    (hStep :
      Cmd.BigStep
        (mergeGeneralLoop hExt f₁ f₂ L₁ L₂) u v) :
    (¬ f₁.Up u → ¬ f₂.Up u → v = u) ∧
      (¬ f₁.Up u → f₂.Up u →
        Cmd.BigStep (.«while» L₂.guard L₂.body)
            (project hExt u) (project hExt v) ∧
          ¬ f₁.Up v ∧ ¬ f₂.Up v) ∧
      (f₁.Up u → ¬ f₂.Up u →
        Cmd.BigStep (mergeTail L₁ L₂)
            (project hExt u) (project hExt v) ∧
          ¬ f₁.Up v ∧ ¬ f₂.Up v) := by
  unfold mergeGeneralLoop at hStep
  generalize hW :
      (Cmd.«while» (Guard.or f₁.test f₂.test)
        (mergeGeneralBody hExt f₁ f₂ L₁ L₂) :
          Cmd D Ω) = W at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G C u hFalse =>
      cases hW
      refine ⟨fun _ _ => rfl, ?_, ?_⟩
      · intro _ hTwo
        exact absurd (Or.inr hTwo : f₁.Up u ∨ f₂.Up u)
          hFalse
      · intro hOne _
        exact absurd (Or.inl hOne : f₁.Up u ∨ f₂.Up u)
          hFalse
  | @while_true G C u m v hEval hBody hLoop ihBody
      ihLoop =>
      cases hW
      have ih := ihLoop rfl
      have hEval' : f₁.Up u ∨ f₂.Up u := hEval
      refine ⟨?_, ?_, ?_⟩
      · intro hOne hTwo
        rcases hEval' with hx | hx
        · exact absurd hx hOne
        · exact absurd hx hTwo
      · intro hOne hTwo
        rcases
          (Cmd.bigStep_ite_iff _ _ _ u m).mp hBody with
          hT | hF
        · exact absurd hT.1 hOne
        · rcases
            (Cmd.bigStep_ite_iff _ _ _ u m).mp hF.2 with
            hG | hnG
          · have hGuard :
                L₂.guard.eval (project hExt u) :=
              (retag_eval_iff hExt L₂.guard u).mp hG.1
            have hRun :
                Cmd.BigStep L₂.body (project hExt u)
                  (project hExt m) :=
              retag_bigStep_project hExt hG.2
            have hOneM : ¬ f₁.Up m := by
              intro hUp
              exact hOne
                ((up_congr_retag hExt hFresh₁
                  hG.2).mp hUp)
            have hTwoM : f₂.Up m :=
              (up_congr_retag hExt hFresh₂ hG.2).mpr hTwo
            rcases ih.2.1 hOneM hTwoM with
              ⟨hLoopRun, hDownOne, hDownTwo⟩
            exact
              ⟨Cmd.BigStep.while_true hGuard hRun
                hLoopRun, hDownOne, hDownTwo⟩
          · have hGuard :
                ¬ L₂.guard.eval (project hExt u) := by
              intro hUp
              exact hnG.1
                ((retag_eval_iff hExt L₂.guard u).mpr
                  hUp)
            have hOneM : ¬ f₁.Up m := by
              intro hUp
              exact hOne
                ((FlagSym.up_congr_of_bigStep_lower_ne
                  hNe hnG.2).mp hUp)
            have hTwoM : ¬ f₂.Up m :=
              FlagSym.not_up_of_bigStep_lower hnG.2
            have hProject :
                project hExt m = project hExt u :=
              project_of_bigStep_lower hExt hFresh₂ hnG.2
            have hVM : v = m := ih.1 hOneM hTwoM
            subst hVM
            refine
              ⟨?_, hOneM, hTwoM⟩
            rw [hProject]
            exact Cmd.BigStep.while_false hGuard
      · intro hOne hTwo
        rcases
          (Cmd.bigStep_ite_iff _ _ _ u m).mp hBody with
          hT | hF
        · rcases
            (Cmd.bigStep_ite_iff _ _ _ u m).mp hT.2 with
            hG | hnG
          · have hGuard :
                L₁.guard.eval (project hExt u) :=
              (retag_eval_iff hExt L₁.guard u).mp hG.1
            have hRun :
                Cmd.BigStep L₁.body (project hExt u)
                  (project hExt m) :=
              retag_bigStep_project hExt hG.2
            have hOneM : f₁.Up m :=
              (up_congr_retag hExt hFresh₁ hG.2).mpr hOne
            have hTwoM : ¬ f₂.Up m := by
              intro hUp
              exact hTwo
                ((up_congr_retag hExt hFresh₂
                  hG.2).mp hUp)
            rcases ih.2.2 hOneM hTwoM with
              ⟨hTailRun, hDownOne, hDownTwo⟩
            refine ⟨?_, hDownOne, hDownTwo⟩
            rcases
              (Cmd.bigStep_seq_iff _ _ (project hExt m)
                (project hExt v)).mp hTailRun with
              ⟨a, hLoopOne, hRest⟩
            exact
              Cmd.BigStep.seq
                (Cmd.BigStep.while_true hGuard hRun
                  hLoopOne)
                hRest
          · have hGuard :
                ¬ L₁.guard.eval (project hExt u) := by
              intro hUp
              exact hnG.1
                ((retag_eval_iff hExt L₁.guard u).mpr
                  hUp)
            rcases
              (Cmd.bigStep_seq_iff _ _ u m).mp
                hnG.2 with ⟨u₁, hLower, hRest₁⟩
            rcases
              (Cmd.bigStep_seq_iff _ _ u₁ m).mp
                hRest₁ with ⟨u₂, hRaise, hRest₂⟩
            rcases
              (Cmd.bigStep_seq_iff _ _ u₂ m).mp
                hRest₂ with ⟨u₃, hClose, hInit⟩
            have hOneTwo : ¬ f₁.Up u₂ := by
              intro hUp
              have hU₁ : f₁.Up u₁ :=
                (FlagSym.up_congr_of_bigStep_raise_ne
                  hNe hRaise).mp hUp
              exact
                (FlagSym.not_up_of_bigStep_lower hLower)
                  hU₁
            have hTwoTwo : f₂.Up u₂ :=
              FlagSym.up_of_bigStep_raise hRaise
            have hOneM : ¬ f₁.Up m := by
              intro hUp
              exact hOneTwo
                ((up_congr_retag hExt hFresh₁ hClose).mp
                  ((up_congr_retag hExt hFresh₁
                    hInit).mp hUp))
            have hTwoM : f₂.Up m :=
              (up_congr_retag hExt hFresh₂ hInit).mpr
                ((up_congr_retag hExt hFresh₂
                  hClose).mpr hTwoTwo)
            rcases ih.2.1 hOneM hTwoM with
              ⟨hLoopRun, hDownOne, hDownTwo⟩
            refine ⟨?_, hDownOne, hDownTwo⟩
            have hP₁ : project hExt u₁ = project hExt u :=
              project_of_bigStep_lower hExt hFresh₁
                hLower
            have hP₂ : project hExt u₂ = project hExt u₁ :=
              project_of_bigStep_raise hExt hFresh₂
                hRaise
            have hCloseRun :
                Cmd.BigStep L₁.close (project hExt u)
                  (project hExt u₃) := by
              have := retag_bigStep_project hExt hClose
              rw [hP₂, hP₁] at this
              exact this
            have hInitRun :
                Cmd.BigStep L₂.init (project hExt u₃)
                  (project hExt m) :=
              retag_bigStep_project hExt hInit
            exact
              Cmd.BigStep.seq
                (Cmd.BigStep.while_false hGuard)
                (Cmd.BigStep.seq hCloseRun
                  (Cmd.BigStep.seq hInitRun hLoopRun))
        · exact absurd hOne hF.1

/-
  Claim A, read backwards: from a state with the second
  flag up, a run of the second loop lifts to a run of the
  merged loop.
-/
theorem mergeGeneral_lift_second
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (hFresh₁ : f₁.sym.1 ∉ Δ.syms)
    (hFresh₂ : f₂.sym.1 ∉ Δ.syms)
    (hNe : f₁.sym ≠ f₂.sym)
    (L₁ L₂ : Framed D Δ)
    {s t : Instance D Δ}
    (hStep :
      Cmd.BigStep (.«while» L₂.guard L₂.body) s t) :
    ∀ u : Instance D Ω,
      project hExt u = s →
      ¬ f₁.Up u → f₂.Up u →
        ∃ v : Instance D Ω,
          Cmd.BigStep
              (mergeGeneralLoop hExt f₁ f₂ L₁ L₂) u v ∧
            project hExt v = t ∧
              ¬ f₁.Up v ∧ ¬ f₂.Up v := by
  generalize hW :
      (Cmd.«while» L₂.guard L₂.body : Cmd D Δ) = W
      at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G C s hFalse =>
      cases hW
      intro u hProj hOne hTwo
      have hLower :
          Cmd.BigStep f₂.lower u
            (Instance.update u f₂.sym
              (f₂.emptyExpr.eval u)) :=
        Cmd.BigStep.assign u f₂.sym f₂.emptyExpr
      set m :=
        Instance.update u f₂.sym
          (f₂.emptyExpr.eval u) with hm
      have hOneM : ¬ f₁.Up m := by
        intro hUp
        exact hOne
          ((FlagSym.up_congr_of_bigStep_lower_ne hNe
            hLower).mp hUp)
      have hTwoM : ¬ f₂.Up m :=
        FlagSym.not_up_of_bigStep_lower hLower
      have hProjM : project hExt m = s := by
        rw [← hProj]
        exact
          project_of_bigStep_lower hExt hFresh₂ hLower
      have hGuardFalse :
          ¬ (L₂.guard.onExtension hExt).eval u := by
        intro hUp
        exact hFalse
          (by
            rw [← hProj]
            exact (retag_eval_iff hExt L₂.guard u).mp hUp)
      refine ⟨m, ?_, hProjM, hOneM, hTwoM⟩
      refine
        Cmd.BigStep.while_true (I₁ := m)
          (Or.inr hTwo : f₁.Up u ∨ f₂.Up u) ?_ ?_
      · refine Cmd.BigStep.ite_false hOne ?_
        exact Cmd.BigStep.ite_false hGuardFalse hLower
      · refine Cmd.BigStep.while_false ?_
        rintro (hx | hx)
        · exact hOneM hx
        · exact hTwoM hx
  | @while_true G C s a t hEval hBody hLoop ihBody
      ihLoop =>
      cases hW
      intro u hProj hOne hTwo
      have hGuard :
          (L₂.guard.onExtension hExt).eval u := by
        refine (retag_eval_iff hExt L₂.guard u).mpr ?_
        rw [hProj]
        exact hEval
      rcases
        retag_bigStep_lift hExt hProj hBody with
        ⟨m, hRun, hProjM⟩
      have hOneM : ¬ f₁.Up m := by
        intro hUp
        exact hOne
          ((up_congr_retag hExt hFresh₁ hRun).mp hUp)
      have hTwoM : f₂.Up m :=
        (up_congr_retag hExt hFresh₂ hRun).mpr hTwo
      rcases ihLoop rfl m hProjM hOneM hTwoM with
        ⟨v, hV, hProjV, hDown⟩
      refine ⟨v, ?_, hProjV, hDown⟩
      refine
        Cmd.BigStep.while_true (I₁ := m)
          (Or.inr hTwo : f₁.Up u ∨ f₂.Up u) ?_ hV
      refine Cmd.BigStep.ite_false hOne ?_
      exact Cmd.BigStep.ite_true hGuard hRun

/-
  Claim B, read backwards: from a state with the first
  flag up, a run of the first phase lifts to a run of the
  merged loop.
-/
theorem mergeGeneral_lift_first
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (hFresh₁ : f₁.sym.1 ∉ Δ.syms)
    (hFresh₂ : f₂.sym.1 ∉ Δ.syms)
    (hNe : f₁.sym ≠ f₂.sym)
    (L₁ L₂ : Framed D Δ)
    {s a : Instance D Δ}
    (hStep :
      Cmd.BigStep (.«while» L₁.guard L₁.body) s a) :
    ∀ t : Instance D Δ,
      Cmd.BigStep
        (.seq L₁.close
          (.seq L₂.init
            (.«while» L₂.guard L₂.body))) a t →
      ∀ u : Instance D Ω,
        project hExt u = s →
        f₁.Up u → ¬ f₂.Up u →
          ∃ v : Instance D Ω,
            Cmd.BigStep
                (mergeGeneralLoop hExt f₁ f₂ L₁ L₂)
                u v ∧
              project hExt v = t ∧
                ¬ f₁.Up v ∧ ¬ f₂.Up v := by
  generalize hW :
      (Cmd.«while» L₁.guard L₁.body : Cmd D Δ) = W
      at hStep
  induction hStep with
  | skip I => cases hW
  | assign I X e => cases hW
  | seq h₁ h₂ ih₁ ih₂ => cases hW
  | ite_true hEval hRun ih => cases hW
  | ite_false hEval hRun ih => cases hW
  | @while_false G C s hFalse =>
      cases hW
      intro t hRest u hProj hOne hTwo
      rcases (Cmd.bigStep_seq_iff _ _ s t).mp hRest with
        ⟨b, hClose, hRest₂⟩
      rcases (Cmd.bigStep_seq_iff _ _ b t).mp hRest₂ with
        ⟨c, hInit, hLoopTwo⟩
      have hLower :
          Cmd.BigStep f₁.lower u
            (Instance.update u f₁.sym
              (f₁.emptyExpr.eval u)) :=
        Cmd.BigStep.assign u f₁.sym f₁.emptyExpr
      set u₁ :=
        Instance.update u f₁.sym
          (f₁.emptyExpr.eval u) with hu₁
      have hRaise :
          Cmd.BigStep f₂.raise u₁
            (Instance.update u₁ f₂.sym
              (f₂.topExpr.eval u₁)) :=
        Cmd.BigStep.assign u₁ f₂.sym f₂.topExpr
      set u₂ :=
        Instance.update u₁ f₂.sym
          (f₂.topExpr.eval u₁) with hu₂
      have hOneTwo : ¬ f₁.Up u₂ := by
        intro hUp
        exact
          (FlagSym.not_up_of_bigStep_lower hLower)
          ((FlagSym.up_congr_of_bigStep_raise_ne hNe
            hRaise).mp hUp)
      have hTwoTwo : f₂.Up u₂ :=
        FlagSym.up_of_bigStep_raise hRaise
      have hProjTwo : project hExt u₂ = s := by
        rw [project_of_bigStep_raise hExt hFresh₂ hRaise,
          project_of_bigStep_lower hExt hFresh₁ hLower,
          hProj]
      rcases
        retag_bigStep_lift hExt hProjTwo hClose with
        ⟨u₃, hCloseRun, hProjThree⟩
      rcases
        retag_bigStep_lift hExt hProjThree hInit with
        ⟨u₄, hInitRun, hProjFour⟩
      have hOneFour : ¬ f₁.Up u₄ := by
        intro hUp
        exact hOneTwo
          ((up_congr_retag hExt hFresh₁ hCloseRun).mp
            ((up_congr_retag hExt hFresh₁ hInitRun).mp
              hUp))
      have hTwoFour : f₂.Up u₄ :=
        (up_congr_retag hExt hFresh₂ hInitRun).mpr
          ((up_congr_retag hExt hFresh₂ hCloseRun).mpr
            hTwoTwo)
      rcases
        mergeGeneral_lift_second hExt f₁ f₂ hFresh₁
          hFresh₂ hNe L₁ L₂ hLoopTwo u₄ hProjFour
          hOneFour hTwoFour with
        ⟨v, hV, hProjV, hDown⟩
      refine ⟨v, ?_, hProjV, hDown⟩
      refine
        Cmd.BigStep.while_true (I₁ := u₄)
          (Or.inl hOne : f₁.Up u ∨ f₂.Up u) ?_ hV
      refine Cmd.BigStep.ite_true hOne ?_
      refine Cmd.BigStep.ite_false ?_ ?_
      · intro hUp
        exact hFalse
          (by
            rw [← hProj]
            exact (retag_eval_iff hExt L₁.guard u).mp hUp)
      · exact
          Cmd.BigStep.seq hLower
            (Cmd.BigStep.seq hRaise
              (Cmd.BigStep.seq hCloseRun hInitRun))
  | @while_true G C s a₁ a hEval hBody hLoop ihBody
      ihLoop =>
      cases hW
      intro t hRest u hProj hOne hTwo
      have hGuard :
          (L₁.guard.onExtension hExt).eval u := by
        refine (retag_eval_iff hExt L₁.guard u).mpr ?_
        rw [hProj]
        exact hEval
      rcases retag_bigStep_lift hExt hProj hBody with
        ⟨m, hRun, hProjM⟩
      have hOneM : f₁.Up m :=
        (up_congr_retag hExt hFresh₁ hRun).mpr hOne
      have hTwoM : ¬ f₂.Up m := by
        intro hUp
        exact hTwo
          ((up_congr_retag hExt hFresh₂ hRun).mp hUp)
      rcases
        ihLoop rfl t hRest m hProjM hOneM hTwoM with
        ⟨v, hV, hProjV, hDown⟩
      refine ⟨v, ?_, hProjV, hDown⟩
      refine
        Cmd.BigStep.while_true (I₁ := m)
          (Or.inl hOne : f₁.Up u ∨ f₂.Up u) ?_ hV
      refine Cmd.BigStep.ite_true hOne ?_
      exact Cmd.BigStep.ite_true hGuard hRun

/- The unfolding of the general merge, spelled out. -/
theorem mergeGeneral_bigStep_iff
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (s t : Instance D Ω) :
    Cmd.BigStep
        (mergeGeneral hExt f₁ f₂ L₁ L₂).unfold s t ↔
      ∃ u v : Instance D Ω,
        Cmd.BigStep
            (.seq (retag hExt L₁.init)
              (.seq f₁.raise f₂.lower)) s u ∧
          Cmd.BigStep
              (mergeGeneralLoop hExt f₁ f₂ L₁ L₂) u v ∧
            Cmd.BigStep (retag hExt L₂.close) v t :=
  Framed.bigStep_unfold_iff _ s t

/- Lemma "Merge", case (iii). -/
theorem mergeGeneral_equivMod
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (hFresh₁ : f₁.sym.1 ∉ Δ.syms)
    (hFresh₂ : f₂.sym.1 ∉ Δ.syms)
    (hNe : f₁.sym ≠ f₂.sym)
    (L₁ L₂ : Framed D Δ) :
    EquivMod hExt (.seq L₁.unfold L₂.unfold)
      (mergeGeneral hExt f₁ f₂ L₁ L₂).unfold := by
  constructor
  · intro s t hRun
    rcases
      (Cmd.bigStep_seq_iff _ _ (project hExt s) t).mp
        hRun with ⟨x, hOne, hTwo⟩
    rcases
      (Framed.bigStep_unfold_iff L₁ (project hExt s)
        x).mp hOne with ⟨x₁, x₂, hInitOne, hLoopOne,
          hCloseOne⟩
    rcases
      (Framed.bigStep_unfold_iff L₂ x t).mp hTwo with
      ⟨x₃, x₄, hInitTwo, hLoopTwo, hCloseTwo⟩
    rcases retag_bigStep_lift hExt rfl hInitOne with
      ⟨u₀, hInitRun, hProjZero⟩
    have hRaise :
        Cmd.BigStep f₁.raise u₀
          (Instance.update u₀ f₁.sym
            (f₁.topExpr.eval u₀)) :=
      Cmd.BigStep.assign u₀ f₁.sym f₁.topExpr
    set u₁ :=
      Instance.update u₀ f₁.sym
        (f₁.topExpr.eval u₀) with hu₁
    have hLower :
        Cmd.BigStep f₂.lower u₁
          (Instance.update u₁ f₂.sym
            (f₂.emptyExpr.eval u₁)) :=
      Cmd.BigStep.assign u₁ f₂.sym f₂.emptyExpr
    set u₂ :=
      Instance.update u₁ f₂.sym
        (f₂.emptyExpr.eval u₁) with hu₂
    have hOneUp : f₁.Up u₂ :=
      (FlagSym.up_congr_of_bigStep_lower_ne hNe
        hLower).mpr
        (FlagSym.up_of_bigStep_raise hRaise)
    have hTwoDown : ¬ f₂.Up u₂ :=
      FlagSym.not_up_of_bigStep_lower hLower
    have hProjTwo : project hExt u₂ = x₁ := by
      rw [project_of_bigStep_lower hExt hFresh₂ hLower,
        project_of_bigStep_raise hExt hFresh₁ hRaise,
        hProjZero]
    have hTail :
        Cmd.BigStep
          (.seq L₁.close
            (.seq L₂.init
              (.«while» L₂.guard L₂.body))) x₂ x₄ :=
      Cmd.BigStep.seq hCloseOne
        (Cmd.BigStep.seq hInitTwo hLoopTwo)
    rcases
      mergeGeneral_lift_first hExt f₁ f₂ hFresh₁ hFresh₂
        hNe L₁ L₂ hLoopOne x₄ hTail u₂ hProjTwo hOneUp
        hTwoDown with ⟨v, hV, hProjV, hDown⟩
    rcases
      retag_bigStep_lift hExt hProjV hCloseTwo with
      ⟨w, hCloseRun, hProjW⟩
    refine ⟨w, ?_, hProjW⟩
    rw [mergeGeneral_bigStep_iff]
    exact
      ⟨u₂, v,
        Cmd.BigStep.seq hInitRun
          (Cmd.BigStep.seq hRaise hLower),
        hV, hCloseRun⟩
  · intro s t hRun
    rcases (mergeGeneral_bigStep_iff hExt f₁ f₂ L₁ L₂ s
      t).mp hRun with ⟨u, v, hInit, hLoop, hClose⟩
    rcases
      flagInit_raise_lower hExt hFresh₁ hFresh₂ hNe
        hInit with ⟨hUpOne, hDownTwo, hInitRun⟩
    rcases
      (mergeGeneral_project hExt f₁ f₂ hFresh₁ hFresh₂
        hNe L₁ L₂ hLoop).2.2 hUpOne hDownTwo with
      ⟨hTail, _, _⟩
    have hCloseRun :
        Cmd.BigStep L₂.close (project hExt v)
          (project hExt t) :=
      retag_bigStep_project hExt hClose
    rcases
      (Cmd.bigStep_seq_iff _ _ (project hExt u)
        (project hExt v)).mp hTail with
      ⟨y₁, hLoopOne, hRest⟩
    rcases
      (Cmd.bigStep_seq_iff _ _ y₁ (project hExt v)).mp
        hRest with ⟨y₂, hCloseOne, hRest₂⟩
    rcases
      (Cmd.bigStep_seq_iff _ _ y₂ (project hExt v)).mp
        hRest₂ with ⟨y₃, hInitTwo, hLoopTwo⟩
    refine (Cmd.bigStep_seq_iff _ _ _ _).mpr ?_
    refine ⟨y₂, ?_, ?_⟩
    · exact
        (Framed.bigStep_unfold_iff L₁ _ y₂).mpr
          ⟨project hExt u, y₁, hInitRun, hLoopOne,
            hCloseOne⟩
    · exact
        (Framed.bigStep_unfold_iff L₂ y₂ _).mpr
          ⟨y₃, project hExt v, hInitTwo, hLoopTwo,
            hCloseRun⟩

/- Both merge flags are down at every terminal state. -/
theorem mergeGeneral_flags_down
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (hFresh₁ : f₁.sym.1 ∉ Δ.syms)
    (hFresh₂ : f₂.sym.1 ∉ Δ.syms)
    (hNe : f₁.sym ≠ f₂.sym)
    (L₁ L₂ : Framed D Δ)
    {s t : Instance D Ω}
    (hRun :
      Cmd.BigStep
        (mergeGeneral hExt f₁ f₂ L₁ L₂).unfold s t) :
    ¬ f₁.Up t ∧ ¬ f₂.Up t := by
  rcases
    (mergeGeneral_bigStep_iff hExt f₁ f₂ L₁ L₂ s t).mp
      hRun with ⟨u, v, hInit, hLoop, hClose⟩
  rcases
    flagInit_raise_lower hExt hFresh₁ hFresh₂ hNe
      hInit with ⟨hUpOne, hDownTwo, _⟩
  rcases
    (mergeGeneral_project hExt f₁ f₂ hFresh₁ hFresh₂ hNe
      L₁ L₂ hLoop).2.2 hUpOne hDownTwo with
    ⟨_, hDownOneV, hDownTwoV⟩
  constructor
  · intro hUp
    exact hDownOneV
      ((up_congr_retag hExt hFresh₁ hClose).mp hUp)
  · intro hUp
    exact hDownTwoV
      ((up_congr_retag hExt hFresh₂ hClose).mp hUp)


@[simp] theorem loopFree_retag_iff
    (hExt : Ω.extensionOf Δ)
    (C : Cmd D Δ) :
    LoopFree (retag hExt C) ↔ LoopFree C := by
  simp [LoopFree]

/- Lemma "Merge", case (i), modulo no flag. -/
theorem mergeIntoPrefix_equivMod
    (hExt : Ω.extensionOf Δ)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₁.IsBase) :
    EquivMod hExt (.seq L₁.unfold L₂.unfold)
      ((mergeIntoPrefix L₁ L₂).retagOn hExt).unfold :=
  equivMod_retag_of_bigStepEquiv hExt
    (mergeIntoPrefix_bigStepEquiv hBase)

/- Lemma "Merge", case (ii), modulo no flag. -/
theorem mergeIntoSuffix_equivMod
    (hExt : Ω.extensionOf Δ)
    {L₁ L₂ : Framed D Δ}
    (hBase : L₂.IsBase) :
    EquivMod hExt (.seq L₁.unfold L₂.unfold)
      ((mergeIntoSuffix L₁ L₂).retagOn hExt).unfold :=
  equivMod_retag_of_bigStepEquiv hExt
    (mergeIntoSuffix_bigStepEquiv hBase)

/- Lemma "Product", modulo no flag. -/
theorem mergeProduct_equivMod
    (hExt : Ω.extensionOf Δ)
    {L₁ L₂ : Framed D Δ}
    (hIndep : Independent L₁.unfold L₂.unfold) :
    EquivMod hExt (.seq L₁.unfold L₂.unfold)
      ((mergeProduct L₁ L₂).retagOn hExt).unfold :=
  equivMod_retag_of_bigStepEquiv hExt
    (mergeProduct_bigStepEquiv hIndep)

/-
  The sequence merge is correct in every case, with the
  case selected by the source-level Booleans.
-/
theorem mergeSeq_equivMod
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (hFresh₁ : f₁.sym.1 ∉ Δ.syms)
    (hFresh₂ : f₂.sym.1 ∉ Δ.syms)
    (hNe : f₁.sym ≠ f₂.sym)
    (L₁ L₂ : Framed D Δ)
    (loopFreeFirst loopFreeSecond independent : Bool)
    (hFirst : loopFreeFirst = true → L₁.IsBase)
    (hSecond : loopFreeSecond = true → L₂.IsBase)
    (hIndep :
      independent = true →
        Independent L₁.unfold L₂.unfold) :
    EquivMod hExt (.seq L₁.unfold L₂.unfold)
      (mergeSeq hExt f₁ f₂ L₁ L₂ loopFreeFirst
        loopFreeSecond independent).unfold := by
  unfold mergeSeq
  cases loopFreeFirst with
  | true =>
      simpa using
        mergeIntoPrefix_equivMod hExt (hFirst rfl)
  | false =>
      cases loopFreeSecond with
      | true =>
          simpa using
            mergeIntoSuffix_equivMod hExt (hSecond rfl)
      | false =>
          cases independent with
          | true =>
              simpa using
                mergeProduct_equivMod hExt (hIndep rfl)
          | false =>
              simpa using
                mergeGeneral_equivMod hExt f₁ f₂
                  hFresh₁ hFresh₂ hNe L₁ L₂

/- Case (i) keeps the loop-free components loop-free. -/
theorem mergeIntoPrefix_loopFreeParts
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (mergeIntoPrefix L₁ L₂).LoopFreeParts := by
  obtain ⟨hInitOne, hBodyOne, hCloseOne⟩ := hOne
  obtain ⟨hInitTwo, hBodyTwo, hCloseTwo⟩ := hTwo
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [mergeIntoPrefix] <;> tauto

/- Case (ii) keeps the loop-free components loop-free. -/
theorem mergeIntoSuffix_loopFreeParts
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (mergeIntoSuffix L₁ L₂).LoopFreeParts := by
  obtain ⟨hInitOne, hBodyOne, hCloseOne⟩ := hOne
  obtain ⟨hInitTwo, hBodyTwo, hCloseTwo⟩ := hTwo
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [mergeIntoSuffix] <;> tauto

/- The product keeps the loop-free components loop-free. -/
theorem mergeProduct_loopFreeParts
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (mergeProduct L₁ L₂).LoopFreeParts := by
  obtain ⟨hInitOne, hBodyOne, hCloseOne⟩ := hOne
  obtain ⟨hInitTwo, hBodyTwo, hCloseTwo⟩ := hTwo
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [mergeProduct, productBody] <;> tauto

/- The general merge is loop-free in its components. -/
theorem mergeGeneral_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    {L₁ L₂ : Framed D Δ}
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (mergeGeneral hExt f₁ f₂ L₁ L₂).LoopFreeParts := by
  obtain ⟨hInitOne, hBodyOne, hCloseOne⟩ := hOne
  obtain ⟨hInitTwo, hBodyTwo, hCloseTwo⟩ := hTwo
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [mergeGeneral, mergeGeneralBody, mergeSwitch,
      FlagSym.raise, FlagSym.lower] <;> tauto

/- Every case of the merge preserves loop-freeness. -/
theorem mergeSeq_loopFreeParts
    (hExt : Ω.extensionOf Δ)
    (f₁ f₂ : FlagSym Ω)
    (L₁ L₂ : Framed D Δ)
    (loopFreeFirst loopFreeSecond independent : Bool)
    (hOne : L₁.LoopFreeParts)
    (hTwo : L₂.LoopFreeParts) :
    (mergeSeq hExt f₁ f₂ L₁ L₂ loopFreeFirst
      loopFreeSecond independent).LoopFreeParts := by
  have hRetag :
      ∀ L : Framed D Δ, L.LoopFreeParts →
        (L.retagOn hExt).LoopFreeParts := by
    intro L hL
    exact
      ⟨(loopFree_retag_iff hExt L.init).mpr hL.1,
        (loopFree_retag_iff hExt L.body).mpr hL.2.1,
        (loopFree_retag_iff hExt L.close).mpr hL.2.2⟩
  unfold mergeSeq
  cases loopFreeFirst with
  | true =>
      exact hRetag _
        (mergeIntoPrefix_loopFreeParts hOne hTwo)
  | false =>
      cases loopFreeSecond with
      | true =>
          exact hRetag _
            (mergeIntoSuffix_loopFreeParts hOne hTwo)
      | false =>
          cases independent with
          | true =>
              exact hRetag _
                (mergeProduct_loopFreeParts hOne hTwo)
          | false =>
              exact
                mergeGeneral_loopFreeParts hExt f₁ f₂
                  hOne hTwo

end Preprocess

end Whiel
