-- Author: Jesse Comer
import Whiel.Cmd.Semantics

/-
  Framed-loop shape theory for Whiel commands.

  Key definitions include:
    * `Whiel.Cmd.LoopFree`
    * `Whiel.Cmd.AssignedAtMostOnceOn`
    * `Whiel.Cmd.LoopOnly`
    * `Whiel.Cmd.loopOnlyParts?`
    * `Whiel.Cmd.FramedLoop`
    * `Whiel.Cmd.BigStep.exists_of_loopFree`

  A framed loop has the shape
  `Init; while G do Body; Close`, with loop-free
  components and a safe initialization block.
-/

------------------------------------------------------------
-- Sequential Command Lists
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Sequential composition of a command list. -/
def seqList :
    List (Cmd D Γ) → Cmd D Γ
| [] => .skip
| C :: Cs => .seq C (seqList Cs)

/- Flatten only top-level sequencing. -/
def flattenSeq :
    Cmd D Γ → List (Cmd D Γ)
| .seq C₁ C₂ =>
    C₁.flattenSeq ++ C₂.flattenSeq
| .skip =>
    []
| C =>
    [C]

/-
  Appending command lists corresponds exactly to one
  sequencing boundary.
-/
theorem bigStep_seqList_append_iff
    (Cs Ds : List (Cmd D Γ))
    (I J : Instance D Γ) :
    BigStep (seqList (Cs ++ Ds)) I J ↔
      ∃ K : Instance D Γ,
        BigStep (seqList Cs) I K ∧
          BigStep (seqList Ds) K J := by
  induction Cs generalizing I J with
  | nil =>
      constructor
      · intro h
        exact
          ⟨I, BigStep.skip I,
            by simpa [seqList] using h⟩
      · rintro ⟨K, hSkip, hDs⟩
        have hK : K = I :=
          (bigStep_skip_iff I K).mp
            (by simpa [seqList] using hSkip)
        subst K
        simpa [seqList] using hDs
  | cons C Cs ih =>
      constructor
      · intro h
        rw [List.cons_append, seqList, bigStep_seq_iff] at h
        rcases h with ⟨K, hC, hTail⟩
        rcases (ih K J).mp hTail with ⟨L, hCs, hDs⟩
        exact
          ⟨L,
            by simpa [seqList] using BigStep.seq hC hCs,
            hDs⟩
      · rintro ⟨K, hHead, hDs⟩
        rw [seqList, bigStep_seq_iff] at hHead
        rcases hHead with ⟨L, hC, hCs⟩
        rw [List.cons_append, seqList, bigStep_seq_iff]
        exact
          ⟨L, hC, (ih L J).mpr ⟨K, hCs, hDs⟩⟩

/-
  Sequencing with a final `skip` is semantically neutral.
-/
theorem bigStep_seq_skip_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep (.seq C .skip) I J ↔ BigStep C I J := by
  rw [bigStep_seq_iff]
  constructor
  · rintro ⟨K, hC, hSkip⟩
    have hJ : J = K :=
      (bigStep_skip_iff K J).mp hSkip
    subst J
    exact hC
  · intro hC
    exact ⟨J, hC, BigStep.skip J⟩

/-
  Flattened top-level sequences are semantically
  equivalent to the source.
-/
theorem bigStep_seqList_flattenSeq_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep (seqList C.flattenSeq) I J ↔
      BigStep C I J := by
  induction C generalizing I J with
  | skip =>
      simp [flattenSeq, seqList]
  | assign X e =>
      change
        BigStep (.seq (.assign X e) .skip) I J ↔
          BigStep (.assign X e : Cmd D Γ) I J
      exact
        bigStep_seq_skip_iff
          (.assign X e : Cmd D Γ) I J
  | seq C₁ C₂ ih₁ ih₂ =>
      rw [flattenSeq, bigStep_seqList_append_iff]
      constructor
      · rintro ⟨K, h₁, h₂⟩
        exact
          BigStep.seq
            ((ih₁ I K).mp h₁)
            ((ih₂ K J).mp h₂)
      · intro h
        rcases (bigStep_seq_iff C₁ C₂ I J).mp h with
          ⟨K, h₁, h₂⟩
        exact
          ⟨K, (ih₁ I K).mpr h₁,
            (ih₂ K J).mpr h₂⟩
  | ite G C₁ C₂ ih₁ ih₂ =>
      change
        BigStep (.seq (.ite G C₁ C₂) .skip) I J ↔
          BigStep (.ite G C₁ C₂ : Cmd D Γ) I J
      exact
        bigStep_seq_skip_iff
          (.ite G C₁ C₂ : Cmd D Γ) I J
  | «while» G C ih =>
      change
        BigStep (.seq (.while G C) .skip) I J ↔
          BigStep (.while G C : Cmd D Γ) I J
      exact bigStep_seq_skip_iff (.while G C : Cmd D Γ) I J

end Cmd

end Whiel

------------------------------------------------------------
-- Loop-Free Commands
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Commands with no syntactic `while` subcommands. -/
def LoopFree :
    Cmd D Γ → Prop
| .skip =>
    True
| .assign _ _ =>
    True
| .seq C₁ C₂ =>
    C₁.LoopFree ∧ C₂.LoopFree
| .ite _ C₁ C₂ =>
    C₁.LoopFree ∧ C₂.LoopFree
| .while _ _ =>
    False

/- `skip` is loop-free. -/
theorem loopFree_skip :
    LoopFree (.skip : Cmd D Γ) :=
  trivial

/- Assignments are loop-free. -/
theorem loopFree_assign
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    LoopFree (.assign X e) :=
  trivial

/- Sequencing preserves loop-freedom. -/
theorem loopFree_seq
    {C₁ C₂ : Cmd D Γ}
    (h₁ : C₁.LoopFree)
    (h₂ : C₂.LoopFree) :
    LoopFree (.seq C₁ C₂) :=
  ⟨h₁, h₂⟩

/- Conditionals preserve loop-freedom. -/
theorem loopFree_ite
    (G : Guard D Γ)
    {C₁ C₂ : Cmd D Γ}
    (h₁ : C₁.LoopFree)
    (h₂ : C₂.LoopFree) :
    LoopFree (.ite G C₁ C₂) :=
  ⟨h₁, h₂⟩

/- Loop-freedom is decidable by structural recursion. -/
def decidableLoopFree :
    (C : Cmd D Γ) → Decidable C.LoopFree
| .skip =>
    isTrue trivial
| .assign _ _ =>
    isTrue trivial
| .seq C₁ C₂ =>
    let d₁ := decidableLoopFree C₁
    let d₂ := decidableLoopFree C₂
    match d₁, d₂ with
    | isTrue h₁, isTrue h₂ =>
        isTrue ⟨h₁, h₂⟩
    | isFalse h₁, _ =>
        isFalse (fun h => h₁ h.1)
    | _, isFalse h₂ =>
        isFalse (fun h => h₂ h.2)
| .ite _ C₁ C₂ =>
    let d₁ := decidableLoopFree C₁
    let d₂ := decidableLoopFree C₂
    match d₁, d₂ with
    | isTrue h₁, isTrue h₂ =>
        isTrue ⟨h₁, h₂⟩
    | isFalse h₁, _ =>
        isFalse (fun h => h₁ h.1)
    | _, isFalse h₂ =>
        isFalse (fun h => h₂ h.2)
| .while _ _ =>
    isFalse (fun h => h)

/- Decidable instance for loop-freedom. -/
instance instDecidableLoopFree
    (C : Cmd D Γ) :
    Decidable C.LoopFree :=
  decidableLoopFree C

/- Boolean wrapper for loop-freedom. -/
def loopFree?
    (C : Cmd D Γ) : Bool :=
  decide C.LoopFree

/- The Boolean loop-freedom check matches `LoopFree`. -/
theorem loopFree?_correct
    (C : Cmd D Γ) :
    C.loopFree? = true ↔ C.LoopFree := by
  simp [loopFree?]

/- Every loop-free command has a terminating run. -/
theorem BigStep.exists_of_loopFree
    (C : Cmd D Γ)
    (hLoopFree : C.LoopFree)
    (I : Instance D Γ) :
    ∃ J : Instance D Γ, BigStep C I J := by
  induction C generalizing I with
  | skip =>
      exact ⟨I, BigStep.skip I⟩
  | assign X e =>
      exact
        ⟨Instance.update I X (e.eval I),
          BigStep.assign I X e⟩
  | seq C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with ⟨h₁, h₂⟩
      rcases ih₁ h₁ I with ⟨K, hStep₁⟩
      rcases ih₂ h₂ K with ⟨J, hStep₂⟩
      exact ⟨J, BigStep.seq hStep₁ hStep₂⟩
  | ite G C₁ C₂ ih₁ ih₂ =>
      rcases hLoopFree with ⟨h₁, h₂⟩
      by_cases hG : G.eval I
      · rcases ih₁ h₁ I with ⟨J, hStep⟩
        exact ⟨J, BigStep.ite_true hG hStep⟩
      · rcases ih₂ h₂ I with ⟨J, hStep⟩
        exact ⟨J, BigStep.ite_false hG hStep⟩
  | «while» =>
      exact False.elim hLoopFree

end Cmd

end Whiel

------------------------------------------------------------
-- Initial Assignment Uniqueness
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- No IDB symbol is assigned in both commands. -/
def DisjointAssignmentsOn
    (C₁ C₂ : Cmd D Γ)
    (IDB : Finset A) : Prop :=
  ∀ X, X ∈ IDB →
    X ∈ C₁.assignedSymbols →
      X ∉ C₂.assignedSymbols

/-
  Syntactic at-most-once assignment on a chosen IDB set.
  Branches are counted together, so this is a conservative
  uniqueness condition for initialization blocks.
-/
def AssignedAtMostOnceOn :
    Cmd D Γ → Finset A → Prop
| .skip, _ =>
    True
| .assign _ _, _ =>
    True
| .seq C₁ C₂, IDB =>
    C₁.AssignedAtMostOnceOn IDB ∧
      C₂.AssignedAtMostOnceOn IDB ∧
        DisjointAssignmentsOn C₁ C₂ IDB
| .ite _ C₁ C₂, IDB =>
    C₁.AssignedAtMostOnceOn IDB ∧
      C₂.AssignedAtMostOnceOn IDB ∧
        DisjointAssignmentsOn C₁ C₂ IDB
| .while _ C, IDB =>
    C.AssignedAtMostOnceOn IDB

/- `skip` assigns no IDB relation. -/
theorem assignedAtMostOnce_skip
    (IDB : Finset A) :
    (.skip : Cmd D Γ).AssignedAtMostOnceOn IDB :=
  trivial

/- One assignment is always at-most-once. -/
theorem assignedAtMostOnce_assign
    (IDB : Finset A)
    (X : Γ.syms)
    (e : RAExpr D Γ (Γ.arity X)) :
    (.assign X e : Cmd D Γ).AssignedAtMostOnceOn IDB :=
  trivial

/- Sequencing preserves at-most-once under disjointness. -/
theorem assignedAtMostOnce_seq
    {IDB : Finset A}
    {C₁ C₂ : Cmd D Γ}
    (h₁ : C₁.AssignedAtMostOnceOn IDB)
    (h₂ : C₂.AssignedAtMostOnceOn IDB)
    (hDis : DisjointAssignmentsOn C₁ C₂ IDB) :
    (.seq C₁ C₂ : Cmd D Γ).AssignedAtMostOnceOn IDB :=
  ⟨h₁, h₂, hDis⟩

/- Conditionals preserve at-most-once under disjointness. -/
theorem assignedAtMostOnce_ite
    {IDB : Finset A}
    (G : Guard D Γ)
    {C₁ C₂ : Cmd D Γ}
    (h₁ : C₁.AssignedAtMostOnceOn IDB)
    (h₂ : C₂.AssignedAtMostOnceOn IDB)
    (hDis : DisjointAssignmentsOn C₁ C₂ IDB) :
    (.ite G C₁ C₂ : Cmd D Γ).AssignedAtMostOnceOn
      IDB :=
  ⟨h₁, h₂, hDis⟩

/-
  Decidable all-symbol disjointness for assigned relation
  names.
-/
def DisjointAssignments
    (C₁ C₂ : Cmd D Γ) : Prop :=
  C₁.assignedSymbols ∩ C₂.assignedSymbols = ∅

/- Decidable instance for assignment disjointness. -/
instance instDecidableDisjointAssignments
    (C₁ C₂ : Cmd D Γ) :
    Decidable (DisjointAssignments C₁ C₂) := by
  unfold DisjointAssignments
  infer_instance

/- Boolean wrapper for assignment disjointness. -/
def disjointAssignments?
    (C₁ C₂ : Cmd D Γ) : Bool :=
  decide (DisjointAssignments C₁ C₂)

/-
  The Boolean disjointness check matches
  `DisjointAssignments`.
-/
theorem disjointAssignments?_correct
    (C₁ C₂ : Cmd D Γ) :
    disjointAssignments? C₁ C₂ = true ↔
      DisjointAssignments C₁ C₂ := by
  simp [disjointAssignments?]

/-
  Syntactic at-most-once assignment over all relation names.
  Branches are counted together, so assigning a symbol in
  both branches fails this conservative preamble-safety
  check.
-/
def AssignedAtMostOnce :
    Cmd D Γ → Prop
| .skip =>
    True
| .assign _ _ =>
    True
| .seq C₁ C₂ =>
    C₁.AssignedAtMostOnce ∧
      C₂.AssignedAtMostOnce ∧
        DisjointAssignments C₁ C₂
| .ite _ C₁ C₂ =>
    C₁.AssignedAtMostOnce ∧
      C₂.AssignedAtMostOnce ∧
        DisjointAssignments C₁ C₂
| .while _ C =>
    C.AssignedAtMostOnce

/-
  At-most-once assignment is decidable by structural
  recursion.
-/
def decidableAssignedAtMostOnce :
    (C : Cmd D Γ) → Decidable C.AssignedAtMostOnce
| .skip =>
    isTrue trivial
| .assign _ _ =>
    isTrue trivial
| .seq C₁ C₂ =>
    match decidableAssignedAtMostOnce C₁,
        decidableAssignedAtMostOnce C₂,
        instDecidableDisjointAssignments C₁ C₂ with
    | isTrue h₁, isTrue h₂, isTrue hDis =>
        isTrue ⟨h₁, h₂, hDis⟩
    | isFalse h₁, _, _ =>
        isFalse (fun h => h₁ h.1)
    | _, isFalse h₂, _ =>
        isFalse (fun h => h₂ h.2.1)
    | _, _, isFalse hDis =>
        isFalse (fun h => hDis h.2.2)
| .ite _ C₁ C₂ =>
    match decidableAssignedAtMostOnce C₁,
        decidableAssignedAtMostOnce C₂,
        instDecidableDisjointAssignments C₁ C₂ with
    | isTrue h₁, isTrue h₂, isTrue hDis =>
        isTrue ⟨h₁, h₂, hDis⟩
    | isFalse h₁, _, _ =>
        isFalse (fun h => h₁ h.1)
    | _, isFalse h₂, _ =>
        isFalse (fun h => h₂ h.2.1)
    | _, _, isFalse hDis =>
        isFalse (fun h => hDis h.2.2)
| .while _ C =>
    decidableAssignedAtMostOnce C

/- Decidable instance for at-most-once assignment. -/
instance instDecidableAssignedAtMostOnce
    (C : Cmd D Γ) :
    Decidable C.AssignedAtMostOnce :=
  decidableAssignedAtMostOnce C

/-
  Boolean wrapper for all-symbol at-most-once assignment.
-/
def assignedAtMostOnce?
    (C : Cmd D Γ) : Bool :=
  decide C.AssignedAtMostOnce

/-
  The Boolean all-symbol at-most-once check matches the
  Prop.
-/
theorem assignedAtMostOnce?_correct
    (C : Cmd D Γ) :
    C.assignedAtMostOnce? = true ↔
      C.AssignedAtMostOnce := by
  simp [assignedAtMostOnce?]

/-
  Preambles accepted for quantifier-safe SP preprocessing.
-/
def PreambleSPSafe
    (C : Cmd D Γ) : Prop :=
  C.LoopFree ∧ C.AssignedAtMostOnce

/- Decidable instance for preamble SP-safety. -/
instance instDecidablePreambleSPSafe
    (C : Cmd D Γ) :
    Decidable C.PreambleSPSafe := by
  unfold PreambleSPSafe
  infer_instance

/- Boolean wrapper for preamble SP-safety. -/
def preambleSPSafe?
    (C : Cmd D Γ) : Bool :=
  decide C.PreambleSPSafe

/-
  The Boolean preamble safety check matches
  `PreambleSPSafe`.
-/
theorem preambleSPSafe?_correct
    (C : Cmd D Γ) :
    C.preambleSPSafe? = true ↔ C.PreambleSPSafe := by
  simp [preambleSPSafe?]

end Cmd

end Whiel

------------------------------------------------------------
-- Framed Loop Shape
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The always-false guard used for degenerate embeddings. -/
def falseGuard : Guard D Γ :=
  .«false»

/-
  Loop-only commands are one top-level loop with loop-free
  body.
-/
def LoopOnly :
    Cmd D Γ → Prop
| .while _ Body =>
    Body.LoopFree
| _ =>
    False

/- Loop-only recognition is decidable by case analysis. -/
def decidableLoopOnly :
    (C : Cmd D Γ) → Decidable C.LoopOnly
| .skip =>
    isFalse (fun h => h)
| .assign _ _ =>
    isFalse (fun h => h)
| .seq _ _ =>
    isFalse (fun h => h)
| .ite _ _ _ =>
    isFalse (fun h => h)
| .while _ Body =>
    instDecidableLoopFree Body

/- Decidable instance for loop-only commands. -/
instance instDecidableLoopOnly
    (C : Cmd D Γ) :
    Decidable C.LoopOnly :=
  decidableLoopOnly C

/- Boolean wrapper for loop-only recognition. -/
def loopOnly?
    (C : Cmd D Γ) : Bool :=
  decide C.LoopOnly

/- The Boolean loop-only check matches the Prop. -/
theorem loopOnly?_correct
    (C : Cmd D Γ) :
    C.loopOnly? = true ↔ C.LoopOnly := by
  simp [loopOnly?]

/- Extract the guard and body of a loop-only command. -/
def loopOnlyParts? :
    Cmd D Γ → Option (Guard D Γ × Cmd D Γ)
| .while G Body =>
    if _hBody : Body.LoopFree then
      some (G, Body)
    else
      none
| _ =>
    none

/-
  Successful extraction gives a loop with loop-free body.
-/
theorem loopOnlyParts?_sound
    {C : Cmd D Γ}
    {G : Guard D Γ}
    {Body : Cmd D Γ}
    (h : C.loopOnlyParts? = some (G, Body)) :
    C = .while G Body ∧ Body.LoopFree := by
  cases C with
  | skip =>
      simp [loopOnlyParts?] at h
  | assign _ _ =>
      simp [loopOnlyParts?] at h
  | seq _ _ =>
      simp [loopOnlyParts?] at h
  | ite _ _ _ =>
      simp [loopOnlyParts?] at h
  | «while» G₀ Body₀ =>
      unfold loopOnlyParts? at h
      change
        (if _hBody : Body₀.LoopFree then
            some (G₀, Body₀)
          else
            none) =
          some (G, Body) at h
      by_cases hBody : Body₀.LoopFree
      · rw [dif_pos hBody] at h
        injection h with hPair
        cases hPair
        exact ⟨rfl, hBody⟩
      · rw [dif_neg hBody] at h
        contradiction

/- The false guard never holds. -/
theorem falseGuard_not_eval
    (I : Instance D Γ) :
    ¬ (falseGuard : Guard D Γ).eval I := by
  rw [Guard.eval_self_iff]
  simp [falseGuard]

/- Canonical framed-loop syntax. -/
def framedLoopCommand
    (Init : Cmd D Γ)
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (Close : Cmd D Γ) :
    Cmd D Γ :=
  .seq (.seq Init (.while G Body)) Close

/- A top-level command list contains a top-level `while`. -/
def ContainsTopLevelWhile :
    List (Cmd D Γ) → Prop
| [] =>
    False
| .while _ _ :: _ =>
    True
| .skip :: Cs =>
    ContainsTopLevelWhile Cs
| .assign _ _ :: Cs =>
    ContainsTopLevelWhile Cs
| .seq _ _ :: Cs =>
    ContainsTopLevelWhile Cs
| .ite _ _ _ :: Cs =>
    ContainsTopLevelWhile Cs

/- Top-level `while` containment is decidable. -/
def decidableContainsTopLevelWhile :
    (Cs : List (Cmd D Γ)) →
      Decidable (ContainsTopLevelWhile Cs)
| [] =>
    isFalse (fun h => h)
| .while _ _ :: _ =>
    isTrue trivial
| .skip :: Cs =>
    decidableContainsTopLevelWhile Cs
| .assign _ _ :: Cs =>
    decidableContainsTopLevelWhile Cs
| .seq _ _ :: Cs =>
    decidableContainsTopLevelWhile Cs
| .ite _ _ _ :: Cs =>
    decidableContainsTopLevelWhile Cs

/- Decidable instance for top-level `while` containment. -/
instance instDecidableContainsTopLevelWhile
    (Cs : List (Cmd D Γ)) :
    Decidable (ContainsTopLevelWhile Cs) :=
  decidableContainsTopLevelWhile Cs

/- Boolean wrapper for top-level `while` containment. -/
def containsTopLevelWhile?
    (Cs : List (Cmd D Γ)) : Bool :=
  decide (ContainsTopLevelWhile Cs)

/- The Boolean top-level loop check matches the Prop. -/
theorem containsTopLevelWhile?_correct
    (Cs : List (Cmd D Γ)) :
    containsTopLevelWhile? Cs = true ↔
      ContainsTopLevelWhile Cs := by
  simp [containsTopLevelWhile?]

/-
  Result of splitting a flattened top-level sequence into
  init commands, exactly one loop, and close commands.
-/
def splitFramedLoopList? :
    List (Cmd D Γ) →
      Option (List (Cmd D Γ) × Guard D Γ ×
        Cmd D Γ × List (Cmd D Γ))
| [] =>
    none
| .while G Body :: Cs =>
    if _hRest : ContainsTopLevelWhile Cs then
      none
    else
      some ([], G, Body, Cs)
| C :: Cs =>
    match splitFramedLoopList? Cs with
    | none =>
        none
    | some (Init, G, Body, Close) =>
        some (C :: Init, G, Body, Close)

/-
  Successful list splitting gives the expected list shape.
-/
theorem splitFramedLoopList?_sound
    {Cs Init : List (Cmd D Γ)}
    {G : Guard D Γ}
    {Body : Cmd D Γ}
    {Close : List (Cmd D Γ)}
    (hSplit :
      splitFramedLoopList? Cs =
        some (Init, G, Body, Close)) :
    Cs = Init ++ (.while G Body :: Close) := by
  induction Cs generalizing Init G Body Close with
  | nil =>
      simp [splitFramedLoopList?] at hSplit
  | cons C Cs ih =>
      cases C with
      | «while» G₀ Body₀ =>
          by_cases hRest : ContainsTopLevelWhile Cs
          · rw [splitFramedLoopList?,
              dif_pos hRest] at hSplit
            contradiction
          · have hSome :
                some
                  (([] : List (Cmd D Γ)),
                    G₀, Body₀, Cs) =
                  some (Init, G, Body, Close) := by
              simpa [splitFramedLoopList?,
                hRest] using hSplit
            rcases hSome with ⟨rfl, rfl, rfl, rfl⟩
            rfl
      | skip =>
          change
            (match splitFramedLoopList? Cs with
            | none => none
            | some (InitTail, G₀, Body₀, Close₀) =>
                some
                  ((.skip : Cmd D Γ) :: InitTail, G₀,
                    Body₀, Close₀)) =
              some (Init, G, Body, Close) at hSplit
          generalize hTail :
            splitFramedLoopList? Cs = tail at hSplit
          cases tail with
          | none =>
              contradiction
          | some p =>
              rcases p with
                ⟨InitTail, G₀, Body₀, Close₀⟩
              cases hSplit
              have hEq := ih hTail
              simpa using
                congrArg
                  (fun tail => (.skip : Cmd D Γ) :: tail)
                  hEq
      | assign X e =>
          change
            (match splitFramedLoopList? Cs with
            | none => none
            | some (InitTail, G₀, Body₀, Close₀) =>
                some
                  ((.assign X e : Cmd D Γ) :: InitTail,
                    G₀, Body₀, Close₀)) =
              some (Init, G, Body, Close) at hSplit
          generalize hTail :
            splitFramedLoopList? Cs = tail at hSplit
          cases tail with
          | none =>
              contradiction
          | some p =>
              rcases p with
                ⟨InitTail, G₀, Body₀, Close₀⟩
              cases hSplit
              have hEq := ih hTail
              simpa using
                congrArg
                  (fun tail =>
                    (.assign X e : Cmd D Γ) :: tail)
                  hEq
      | seq C₁ C₂ =>
          change
            (match splitFramedLoopList? Cs with
            | none => none
            | some (InitTail, G₀, Body₀, Close₀) =>
                some
                  ((.seq C₁ C₂ : Cmd D Γ) :: InitTail,
                    G₀, Body₀, Close₀)) =
              some (Init, G, Body, Close) at hSplit
          generalize hTail :
            splitFramedLoopList? Cs = tail at hSplit
          cases tail with
          | none =>
              contradiction
          | some p =>
              rcases p with
                ⟨InitTail, G₀, Body₀, Close₀⟩
              cases hSplit
              have hEq := ih hTail
              simpa using
                congrArg
                  (fun tail =>
                    (.seq C₁ C₂ : Cmd D Γ) :: tail)
                  hEq
      | ite G₀ C₁ C₂ =>
          change
            (match splitFramedLoopList? Cs with
            | none => none
            | some (InitTail, G₁, Body₀, Close₀) =>
                some
                  ((.ite G₀ C₁ C₂ : Cmd D Γ) ::
                    InitTail, G₁, Body₀, Close₀)) =
              some (Init, G, Body, Close) at hSplit
          generalize hTail :
            splitFramedLoopList? Cs = tail at hSplit
          cases tail with
          | none =>
              contradiction
          | some p =>
              rcases p with
                ⟨InitTail, G₁, Body₀, Close₀⟩
              cases hSplit
              have hEq := ih hTail
              simpa using
                congrArg
                  (fun tail =>
                    ((.ite G₀ C₁ C₂ :
                      Cmd D Γ) :: tail))
                  hEq

/-
  Extract framed-loop components when the safety checks
  pass.
-/
def framedLoopParts?
    (C : Cmd D Γ) :
    Option
      (Cmd D Γ × Guard D Γ × Cmd D Γ ×
        Cmd D Γ) :=
  match splitFramedLoopList? C.flattenSeq with
  | none =>
      none
  | some (InitList, G, Body, CloseList) =>
      let Init := seqList InitList
      let Close := seqList CloseList
      if _hInit : Init.PreambleSPSafe then
        if _hBody : Body.LoopFree then
          if _hClose : Close.LoopFree then
            some (Init, G, Body, Close)
          else
            none
        else
          none
      else
        none

/- A command is recognized as a framed loop. -/
def FramedLoop
    (C : Cmd D Γ) : Prop :=
  ∃ Init : Cmd D Γ,
    ∃ G : Guard D Γ,
      ∃ Body Close : Cmd D Γ,
        C.framedLoopParts? = some (Init, G, Body, Close)

/- Recognition as a framed loop is decidable. -/
instance instDecidableFramedLoop
    (C : Cmd D Γ) :
    Decidable C.FramedLoop :=
  match h : C.framedLoopParts? with
  | none =>
      isFalse (by
        rintro ⟨Init, G, Body, Close, hParts⟩
        rw [h] at hParts
        contradiction)
  | some (Init, G, Body, Close) =>
      isTrue ⟨Init, G, Body, Close, h⟩

/-
  A split command list is semantically equivalent to its
  framed command.
-/
theorem bigStep_seqList_framedLoopParts_iff
    (initList : List (Cmd D Γ))
    (G : Guard D Γ)
    (Body : Cmd D Γ)
    (closeList : List (Cmd D Γ))
    (I J : Instance D Γ) :
    BigStep
        (seqList (initList ++ (.while G Body :: closeList)))
        I J ↔
      BigStep
        (framedLoopCommand
          (seqList initList) G Body (seqList closeList))
        I J := by
  rw [bigStep_seqList_append_iff]
  unfold framedLoopCommand
  rw [bigStep_seq_iff]
  constructor
  · rintro ⟨K, hInit, hLoopClose⟩
    change
      BigStep (.seq (.while G Body) (seqList closeList)) K J
        at hLoopClose
    rw [bigStep_seq_iff] at hLoopClose
    rcases hLoopClose with ⟨L, hLoop, hClose⟩
    exact ⟨L, BigStep.seq hInit hLoop, hClose⟩
  · rintro ⟨L, hInitLoop, hClose⟩
    rw [bigStep_seq_iff] at hInitLoop
    rcases hInitLoop with ⟨K, hInit, hLoop⟩
    have hLoopClose :
        BigStep
          (seqList
            ((.while G Body : Cmd D Γ) :: closeList))
          K J := by
      change
        BigStep
          (.seq (.while G Body) (seqList closeList))
          K J
      exact BigStep.seq hLoop hClose
    exact ⟨K, hInit, hLoopClose⟩

/-
  Successful component extraction gives a framed-loop run.
-/
theorem framedLoopParts?_sound
    {C : Cmd D Γ}
    {Init : Cmd D Γ}
    {G : Guard D Γ}
    {Body Close : Cmd D Γ}
    (h : C.framedLoopParts? = some (Init, G, Body, Close)) :
    Init.PreambleSPSafe ∧
      Body.LoopFree ∧
        Close.LoopFree ∧
          ∀ I J : Instance D Γ,
            BigStep C I J ↔
              BigStep
                (framedLoopCommand Init G Body Close)
                I J := by
  unfold framedLoopParts? at h
  generalize hSplit :
    splitFramedLoopList? C.flattenSeq = splitOpt at h
  cases splitOpt with
  | none =>
      contradiction
  | some parts =>
      rcases parts with
        ⟨InitList, G₀, Body₀, CloseList⟩
      dsimp only at h
      by_cases hInit :
          (seqList InitList).PreambleSPSafe
      · have hAfterInit :
            (if hBody : Body₀.LoopFree then
              if hClose :
                  (seqList CloseList).LoopFree then
                some
                  (seqList InitList, G₀, Body₀,
                    seqList CloseList)
              else
                none
            else
              none) = some (Init, G, Body, Close) := by
          simpa [hInit] using h
        by_cases hBody : Body₀.LoopFree
        · have hAfterBody :
              (if hClose :
                  (seqList CloseList).LoopFree then
                some
                  (seqList InitList, G₀, Body₀,
                    seqList CloseList)
              else
                none) = some (Init, G, Body, Close) := by
            simpa [hBody] using hAfterInit
          by_cases hClose :
              (seqList CloseList).LoopFree
          · have hSome :
                some
                  (seqList InitList, G₀, Body₀,
                    seqList CloseList) =
                  some (Init, G, Body, Close) := by
              simpa [hClose] using hAfterBody
            cases hSome
            refine ⟨hInit, hBody, hClose, ?_⟩
            intro I J
            have hList :
                C.flattenSeq =
                  InitList ++
                    (.while G Body :: CloseList) :=
              splitFramedLoopList?_sound hSplit
            have hFlat :=
              bigStep_seqList_flattenSeq_iff C I J
            calc
              BigStep C I J
                  ↔ BigStep (seqList C.flattenSeq) I J :=
                    hFlat.symm
              _ ↔ BigStep
                    (seqList
                      (InitList ++
                        (.while G Body :: CloseList)))
                    I J := by
                      simp [hList]
              _ ↔ BigStep
                    (framedLoopCommand
                      (seqList InitList)
                      G
                      Body
                      (seqList CloseList))
                    I J :=
                      bigStep_seqList_framedLoopParts_iff
                        InitList G Body CloseList I J
          · rw [dif_neg hClose] at hAfterBody
            contradiction
        · rw [dif_neg hBody] at hAfterInit
          contradiction
      · rw [dif_neg hInit] at h
        contradiction

/-
  Convert a framed loop to its loop command.
-/
def toLoopOnly?
    (C : Cmd D Γ) :
    Option (Cmd D Γ) :=
  match C.framedLoopParts? with
  | none =>
      none
  | some (_Init, G, Body, _Close) =>
      some (.while G Body)

/- Successful conversion produces a loop-only command. -/
theorem toLoopOnly?_sound
    {C L : Cmd D Γ}
    (h : C.toLoopOnly? = some L) :
    L.LoopOnly := by
  unfold toLoopOnly? at h
  generalize hParts :
    C.framedLoopParts? = parts at h
  cases parts with
  | none =>
      contradiction
  | some p =>
      rcases p with ⟨Init, G, Body, Close⟩
      cases h
      exact (framedLoopParts?_sound hParts).2.1

/-
  Successful conversion implies that the source is framed.
-/
theorem framedLoop_of_toLoopOnly?
    {C L : Cmd D Γ}
    (h : C.toLoopOnly? = some L) :
    C.FramedLoop := by
  unfold toLoopOnly? at h
  generalize hParts :
    C.framedLoopParts? = parts at h
  cases parts with
  | none =>
      contradiction
  | some p =>
      rcases p with ⟨Init, G, Body, Close⟩
      exact ⟨Init, G, Body, Close, hParts⟩

/-
  A command is in framed-loop shape for an IDB set when the
  initialization, body, and close blocks are loop-free, and
  initialization assigns each IDB symbol at most once.
-/
def FramedLoopShape
    (C : Cmd D Γ)
    (IDB : Finset A) : Prop :=
  ∃ Init : Cmd D Γ,
    ∃ G : Guard D Γ,
      ∃ Body Close : Cmd D Γ,
        Init.LoopFree ∧
          Init.AssignedAtMostOnceOn IDB ∧
            Body.LoopFree ∧
              Close.LoopFree ∧
                C = framedLoopCommand Init G Body Close

/- Explicit framed-loop commands satisfy the shape. -/
theorem framedLoopCommand_shape
    (IDB : Finset A)
    {Init Body Close : Cmd D Γ}
    (G : Guard D Γ)
    (hInit : Init.LoopFree)
    (hInitOnce : Init.AssignedAtMostOnceOn IDB)
    (hBody : Body.LoopFree)
    (hClose : Close.LoopFree) :
    (framedLoopCommand Init G Body Close).FramedLoopShape
      IDB := by
  exact
    ⟨Init, G, Body, Close,
      hInit, hInitOnce, hBody, hClose, rfl⟩

/- Embed a command after a false loop. -/
def degenerateFramedLoop
    (C : Cmd D Γ) :
    Cmd D Γ :=
  framedLoopCommand .skip falseGuard .skip C

/-
  Loop-free commands have a degenerate framed-loop shape.
-/
theorem degenerateFramedLoop_shape
    (IDB : Finset A)
    {C : Cmd D Γ}
    (hC : C.LoopFree) :
    C.degenerateFramedLoop.FramedLoopShape IDB := by
  unfold degenerateFramedLoop
  exact framedLoopCommand_shape
    IDB falseGuard
    loopFree_skip
    (assignedAtMostOnce_skip IDB)
    loopFree_skip
    hC

end Cmd

end Whiel

-- Degenerate Framed-Loop Semantics
------------------------------------------------------------

namespace Whiel

namespace Cmd

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The degenerate false loop never takes an iteration. -/
theorem bigStep_falseLoop_iff
    (I J : Instance D Γ) :
    BigStep (.while falseGuard (.skip : Cmd D Γ)) I J ↔
      J = I := by
  rw [bigStep_while_iff]
  constructor
  · intro h
    cases h with
    | inl hFalse =>
        exact hFalse.2
    | inr hTrue =>
        rcases hTrue with ⟨_, hGuard, _hStep, _hLoop⟩
        exact False.elim hGuard
  · intro h
    rw [h]
    exact Or.inl ⟨falseGuard_not_eval I, rfl⟩

/- Degenerate embedding is semantically equivalent. -/
theorem degenerateFramedLoop_bigStep_iff
    (C : Cmd D Γ)
    (I J : Instance D Γ) :
    BigStep C.degenerateFramedLoop I J ↔
      BigStep C I J := by
  unfold degenerateFramedLoop framedLoopCommand
  rw [bigStep_seq_iff]
  constructor
  · rintro ⟨K, hInitLoop, hClose⟩
    rw [bigStep_seq_iff] at hInitLoop
    rcases hInitLoop with ⟨L, hSkip, hLoop⟩
    have hL : L = I :=
      (bigStep_skip_iff I L).mp hSkip
    subst L
    have hK : K = I :=
      (bigStep_falseLoop_iff I K).mp hLoop
    subst K
    exact hClose
  · intro hC
    refine ⟨I, ?_, hC⟩
    rw [bigStep_seq_iff]
    refine ⟨I, BigStep.skip I, ?_⟩
    exact BigStep.while_false (falseGuard_not_eval I)

end Cmd

end Whiel
