import Whiel.Cmd.Semantics

/-
  This file contains shared support for Datalog-to-Whiel
  translations.

  Key definitions include:
    * `Datalog.WhielCompiler.seqList`
    * `Datalog.WhielCompiler.andList`
    * `Datalog.WhielCompiler.orList`

  These helpers are construction support for concrete
  translations such as naive and Gauss-Seidel evaluation.
-/

------------------------------------------------------------
-- Command and Guard Lists
------------------------------------------------------------

namespace Datalog

namespace WhielCompiler

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Sequential composition of a command list. -/
def seqList :
    List (Whiel.Cmd D Γ) → Whiel.Cmd D Γ
| [] => .skip
| C :: Cs => .seq C (seqList Cs)

/- Conjunction of a guard list. -/
def andList :
    List (Whiel.Guard D Γ) → Whiel.Guard D Γ
| [] => .«true»
| G :: Gs => .and G (andList Gs)

/- Disjunction of a guard list. -/
def orList :
    List (Whiel.Guard D Γ) → Whiel.Guard D Γ
| [] => .«false»
| G :: Gs => .or G (orList Gs)

/- Empty command lists execute as `skip`. -/
theorem seqList_nil_bigStep
    (J : Instance D Γ) :
    Whiel.Cmd.BigStep
      (seqList ([] : List (Whiel.Cmd D Γ)))
      J J := by
  simp [seqList]

/-
  Consing a command corresponds to one sequential big-
  step.
-/
theorem seqList_cons_bigStep
    {C : Whiel.Cmd D Γ}
    {Cs : List (Whiel.Cmd D Γ)}
    {I J K : Instance D Γ}
    (hC : Whiel.Cmd.BigStep C I J)
    (hCs : Whiel.Cmd.BigStep (seqList Cs) J K) :
    Whiel.Cmd.BigStep (seqList (C :: Cs)) I K := by
  simpa [seqList] using Whiel.Cmd.BigStep.seq hC hCs

/-
  Appending command lists corresponds to sequential big-
  steps.
-/
theorem seqList_append_bigStep
    {Cs Ds : List (Whiel.Cmd D Γ)}
    {I J K : Instance D Γ}
    (hCs : Whiel.Cmd.BigStep (seqList Cs) I J)
    (hDs : Whiel.Cmd.BigStep (seqList Ds) J K) :
    Whiel.Cmd.BigStep (seqList (Cs ++ Ds)) I K := by
  induction Cs generalizing I J with
  | nil =>
      rw [List.nil_append]
      rw [seqList] at hCs
      rw [Whiel.Cmd.bigStep_skip_iff] at hCs
      simpa [hCs] using hDs
  | cons C Cs ih =>
      rw [List.cons_append]
      rw [seqList] at hCs
      rw [Whiel.Cmd.bigStep_seq_iff] at hCs
      rcases hCs with ⟨M, hC, hCs⟩
      exact seqList_cons_bigStep hC (ih hCs hDs)

/-
  A raw symbol is assigned by a sequential command list exactly
  when it is assigned by one command in the list.
-/
theorem seqList_assignedSymbols_mem
    (Cs : List (Whiel.Cmd D Γ))
    (x : A) :
    x ∈ (seqList Cs).assignedSymbols ↔
      ∃ C : Whiel.Cmd D Γ, C ∈ Cs ∧
        x ∈ C.assignedSymbols := by
  induction Cs with
  | nil =>
      simp [seqList, Whiel.Cmd.assignedSymbols]
  | cons C Cs ih =>
      constructor
      · intro hx
        have hx' :
            x ∈ C.assignedSymbols ∨
              x ∈ (seqList Cs).assignedSymbols := by
          simpa [seqList, Whiel.Cmd.assignedSymbols]
            using hx
        rcases hx' with hxC | hxCs
        · exact ⟨C, by simp, hxC⟩
        · rcases ih.mp hxCs with ⟨C', hC', hxC'⟩
          exact ⟨C', by simp [hC'], hxC'⟩
      · rintro ⟨C', hC', hxC'⟩
        rcases List.mem_cons.mp hC' with hEq | hTail
        · subst hEq
          simp [seqList, Whiel.Cmd.assignedSymbols, hxC']
        · have hxTail :
              x ∈ (seqList Cs).assignedSymbols :=
            ih.mpr ⟨C', hTail, hxC'⟩
          simp [seqList, Whiel.Cmd.assignedSymbols, hxTail]

theorem andList_eval_iff
    (Gs : List (Whiel.Guard D Γ))
    (J : Instance D Γ) :
    Whiel.Guard.eval (andList Gs) J ↔
      ∀ G : Whiel.Guard D Γ, G ∈ Gs →
        Whiel.Guard.eval G J := by
  induction Gs with
  | nil =>
      simp [andList]
  | cons G Gs ih =>
      constructor
      · intro h H hH
        rcases List.mem_cons.mp hH with hEq | hMem
        · subst hEq
          exact h.1
        · exact ih.mp h.2 H hMem
      · intro h
        constructor
        · exact h G (by simp)
        · exact ih.mpr (fun H hH => h H (by simp [hH]))

theorem orList_eval_iff
    (Gs : List (Whiel.Guard D Γ))
    (J : Instance D Γ) :
    Whiel.Guard.eval (orList Gs) J ↔
      ∃ G : Whiel.Guard D Γ, G ∈ Gs ∧
        Whiel.Guard.eval G J := by
  induction Gs with
  | nil =>
      simp [orList]
  | cons G Gs ih =>
      constructor
      · intro h
        rcases h with hG | hRest
        · exact ⟨G, by simp, hG⟩
        · rcases ih.mp hRest with ⟨H, hH, hEval⟩
          exact ⟨H, by simp [hH], hEval⟩
      · rintro ⟨H, hH, hEval⟩
        rcases List.mem_cons.mp hH with hEq | hMem
        · subst hEq
          exact Or.inl hEval
        · exact Or.inr (ih.mpr ⟨H, hMem, hEval⟩)

end WhielCompiler

end Datalog
