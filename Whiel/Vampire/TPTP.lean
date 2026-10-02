-- Author: Jesse Comer
import Databases.RelCalc.ToFOL
import Whiel.Vampire.SolverName

/-
  Pure TPTP rendering for closed FOL entailments.

  Key definitions:
    * `Whiel.Vampire.TPTP.problem`
    * `Whiel.Vampire.TPTP.relCalcAxiomBlock`
    * `Whiel.Vampire.TPTP.relCalcConjectureDecl`

  Lean has already built the FOL sentences before they reach
  this file. The definitions here only print those sentences
  as TPTP text and give RelCalc support axioms stable names.

  A symbol's solver-facing name comes from `SolverName`, so
  naming is one application of a function and never a
  freshening pass. Because nothing is renamed apart any more,
  an environment can be malformed: `NameEnv.wellFormed`
  decides whether it is, the production carriers prove it
  never fails for them, and the two consumers that would be
  harmed by a bad environment refuse one — `appendBindings?`
  for a name a worker is offered, and `exact_reconstruction`
  for the telescope a certificate reads.
-/

------------------------------------------------------------
-- Identifier Rendering
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace TPTP

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/- TPTP variable name. -/
def varName
    (x : Var) : String :=
  "X" ++ reprStr x

/- Join strings with a separator. -/
def joinSep
    (sep : String) :
    List String → String
| [] => ""
| s :: ss => ss.foldl (fun acc t => acc ++ sep ++ t) s

/- Does a list of strings contain a string? -/
def containsString
    (xs : List String)
    (x : String) : Bool :=
  xs.any (fun y => y == x)

/- Drop the symbols already seen, keeping the first of each. -/
def eraseDupsFrom
    {α : Type}
    [DecidableEq α]
    (seen : List α) :
    List α → List α
| [] => []
| x :: xs =>
    if x ∈ seen then
      eraseDupsFrom seen xs
    else
      x :: eraseDupsFrom (x :: seen) xs

/- Remove duplicates while preserving first occurrences. -/
def eraseDupsPreserve
    {α : Type}
    [DecidableEq α]
    (xs : List α) :
    List α :=
  eraseDupsFrom [] xs

private theorem not_mem_eraseDupsFrom
    {α : Type}
    [DecidableEq α]
    {y : α}
    (xs seen : List α)
    (hSeen : y ∈ seen) :
    y ∉ eraseDupsFrom seen xs := by
  induction xs generalizing seen with
  | nil => simp [eraseDupsFrom]
  | cons x xs ih =>
      unfold eraseDupsFrom
      split
      · exact ih seen hSeen
      · rename_i hFresh
        simp only [List.mem_cons, not_or]
        refine ⟨?_, ih (x :: seen) (by simp [hSeen])⟩
        intro hEq
        exact hFresh (hEq ▸ hSeen)

private theorem eraseDupsFrom_nodup
    {α : Type}
    [DecidableEq α]
    (xs seen : List α) :
    (eraseDupsFrom seen xs).Nodup := by
  induction xs generalizing seen with
  | nil => simp [eraseDupsFrom]
  | cons x xs ih =>
      unfold eraseDupsFrom
      split
      · exact ih seen
      · exact List.nodup_cons.mpr
          ⟨not_mem_eraseDupsFrom xs (x :: seen) (by simp),
            ih (x :: seen)⟩

/- Deduplication leaves each symbol once. -/
theorem eraseDupsPreserve_nodup
    {α : Type}
    [DecidableEq α]
    (xs : List α) :
    (eraseDupsPreserve xs).Nodup :=
  eraseDupsFrom_nodup xs []

/-
  Name each distinct symbol, in first-occurrence order. The
  order is what the binder telescope, the symbol map and the
  certificate literal read; the names themselves come from
  the carrier and are never adjusted here.
-/
def assignSolverNames
    {α : Type}
    [DecidableEq α]
    [SolverName α]
    (xs : List α) :
    List (α × String) :=
  (eraseDupsPreserve xs).map (fun x => (x, solverName x))

/- The names assigned, in order. -/
theorem map_snd_assignSolverNames
    {α : Type}
    [DecidableEq α]
    [SolverName α]
    (xs : List α) :
    (assignSolverNames xs).map Prod.snd =
      (eraseDupsPreserve xs).map solverName := by
  simp [assignSolverNames, List.map_map, Function.comp_def]

/- A lawful carrier assigns each symbol a distinct name. -/
theorem nodup_map_snd_assignSolverNames
    {α : Type}
    [DecidableEq α]
    [SolverName α]
    [LawfulSolverName α]
    (xs : List α) :
    ((assignSolverNames xs).map Prod.snd).Nodup := by
  rw [map_snd_assignSolverNames]
  exact (eraseDupsPreserve_nodup xs).map
    LawfulSolverName.solverName_injective

/- A lawful carrier assigns only legal identifiers. -/
theorem all_legalTptpName_assignSolverNames
    {α : Type}
    [DecidableEq α]
    [SolverName α]
    [LawfulSolverName α]
    (xs : List α) :
    ((assignSolverNames xs).map Prod.snd).all
      legalTptpName = true := by
  rw [map_snd_assignSolverNames, List.all_eq_true]
  intro name hName
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hName
  exact LawfulSolverName.legalTptpName_solverName x

/- Every assigned name is some symbol's name. -/
theorem exists_of_mem_map_snd_assignSolverNames
    {α : Type}
    [DecidableEq α]
    [SolverName α]
    {xs : List α}
    {name : String}
    (hName : name ∈ (assignSolverNames xs).map Prod.snd) :
    ∃ x : α, solverName x = name := by
  rw [map_snd_assignSolverNames] at hName
  obtain ⟨x, _, hx⟩ := List.mem_map.mp hName
  exact ⟨x, hx⟩

end TPTP
end Vampire
end Whiel

------------------------------------------------------------
-- Name Environments
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace TPTP

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/-
  The symbols one rendered problem declares, in order, with
  the name each is rendered under. Order is load-bearing: it
  is the order of the binder telescope a certificate reads,
  of the symbol-map comment, and of the revisioned state a
  worker replays.
-/
structure NameEnv
    (A F : Type)
    [RelationNames A]
    [FunctionNames F] where
  relNames : List (A × String)
  funNames : List (F × String)

mutual
/- Function symbols occurring in a term. -/
  def termFunctions :
      FOL.Term Λ → List F
  | .var _ => []
  | .func f args => f.1 :: termListFunctions args

/- Function symbols occurring in a term list. -/
  def termListFunctions :
      {n : Nat} → FOL.TermList Λ n → List F
  | _, .nil => []
  | _, .cons t ts =>
      termFunctions t ++ termListFunctions ts
end

/- Relation symbols occurring in a formula. -/
def formulaRelations :
    FOL.Formula Λ → List A
| .top => []
| .bot => []
| .eq _ _ => []
| .rel r _ => [r.1]
| .and φ ψ => formulaRelations φ ++ formulaRelations ψ
| .or φ ψ => formulaRelations φ ++ formulaRelations ψ
| .not φ => formulaRelations φ
| .imp φ ψ => formulaRelations φ ++ formulaRelations ψ
| .iff φ ψ => formulaRelations φ ++ formulaRelations ψ
| .forall_ _ φ => formulaRelations φ
| .exists_ _ φ => formulaRelations φ

/- Function symbols occurring in a formula. -/
def formulaFunctions :
    FOL.Formula Λ → List F
| .top => []
| .bot => []
| .eq t u => termFunctions t ++ termFunctions u
| .rel _ ts => termListFunctions ts
| .and φ ψ => formulaFunctions φ ++ formulaFunctions ψ
| .or φ ψ => formulaFunctions φ ++ formulaFunctions ψ
| .not φ => formulaFunctions φ
| .imp φ ψ => formulaFunctions φ ++ formulaFunctions ψ
| .iff φ ψ => formulaFunctions φ ++ formulaFunctions ψ
| .forall_ _ φ => formulaFunctions φ
| .exists_ _ φ => formulaFunctions φ

namespace NameEnv

/- Strict relation-name lookup. -/
def rel?
    (env : NameEnv A F)
    (r : A) :
    Option String :=
  (env.relNames.find? (fun p => decide (p.1 = r))).map Prod.snd

/- Strict function-name lookup. -/
def funName?
    (env : NameEnv A F)
    (f : F) :
    Option String :=
  (env.funNames.find? (fun p => decide (p.1 = f))).map Prod.snd

/- One environment is an append-only extension of another. -/
def AppendOnly
    (old new : NameEnv A F) : Prop :=
  old.relNames <+: new.relNames ∧
    old.funNames <+: new.funNames

/- Append-only extension is reflexive. -/
theorem AppendOnly.refl
    (env : NameEnv A F) : AppendOnly env env := by
  exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

/- Append-only extension is transitive. -/
theorem AppendOnly.trans
    {first second third : NameEnv A F}
    (h₁ : AppendOnly first second)
    (h₂ : AppendOnly second third) :
    AppendOnly first third :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/- All names already reserved by an environment. -/
def usedNames
    (env : NameEnv A F) : List String :=
  env.relNames.map Prod.snd ++ env.funNames.map Prod.snd

/-
  Whether an environment may be handed to a solver: every
  name it declares is a legal identifier, and no name is
  declared twice — not for two relations, not for two
  functions, and not once for each.

  Nothing is renamed apart any more, so this predicate is
  what collision suffixing used to arrange. It is decided,
  not assumed: the production carriers prove below that it
  holds of every environment built from them, and a carrier
  without such a proof is caught by the two consumers that
  reject a bad environment rather than render one.

  This decides legality and the absence of repeats only.
  Exclusion of TPTP keywords (`isReservedWord`) and of
  Vampire's introduced-symbol shape (`isIntroducedShape`) are
  not part of this predicate; they are separate theorems
  proved of the production carriers' names
  (`Vampire/SolverName.lean`), not conditions this function
  checks.
-/
def wellFormed
    (env : NameEnv A F) : Bool :=
  env.usedNames.all legalTptpName &&
    decide env.usedNames.Nodup

/- Append one explicit relation assignment when consistent. -/
def appendRelation?
    (env : NameEnv A F)
    (relation : A)
    (name : String) :
    Option (NameEnv A F) :=
  match env.rel? relation with
  | some old => if old = name then some env else none
  | none =>
      if containsString env.usedNames name then
        none
      else
        some { env with
          relNames := env.relNames ++ [(relation, name)] }

/- Append one explicit function assignment when consistent. -/
def appendFunction?
    (env : NameEnv A F)
    (function : F)
    (name : String) :
    Option (NameEnv A F) :=
  match env.funName? function with
  | some old => if old = name then some env else none
  | none =>
      if containsString env.usedNames name then
        none
      else
        some { env with
          funNames := env.funNames ++ [(function, name)] }

/- Append explicit relation assignments. -/
def appendRelationBindings?
    (env : NameEnv A F)
    : List (A × String) → Option (NameEnv A F)
| [] => some env
| binding :: bindings => do
    let next ← env.appendRelation? binding.1 binding.2
    next.appendRelationBindings? bindings

/- Append explicit function assignments. -/
def appendFunctionBindings?
    (env : NameEnv A F)
    : List (F × String) → Option (NameEnv A F)
| [] => some env
| binding :: bindings => do
    let next ← env.appendFunction? binding.1 binding.2
    next.appendFunctionBindings? bindings

/- Append explicit Rust-owned symbol assignments. -/
def appendBindings?
    (env : NameEnv A F)
    (relations : List (A × String))
    (functions : List (F × String)) :
    Option (NameEnv A F) := do
  let withRelations ← env.appendRelationBindings? relations
  withRelations.appendFunctionBindings? functions

/- A successful explicit relation append is append-only. -/
theorem appendRelation?_appendOnly
    (env new : NameEnv A F)
    (relation : A)
    (name : String)
    (hAppend : env.appendRelation? relation name = some new) :
    AppendOnly env new := by
  cases hLookup : env.rel? relation with
  | none =>
      by_cases hUsed : containsString env.usedNames name = true
      · simp only [appendRelation?, hLookup, hUsed, ↓reduceIte]
          at hAppend
        cases hAppend
      · simp only [appendRelation?, hLookup, hUsed]
          at hAppend
        cases hAppend
        exact ⟨List.prefix_append _ _, ⟨[], by simp⟩⟩
  | some old =>
      by_cases hSame : old = name
      · simp only [appendRelation?, hLookup, hSame, ↓reduceIte]
          at hAppend
        cases hAppend
        exact AppendOnly.refl env
      · simp only [appendRelation?, hLookup, hSame, ↓reduceIte]
          at hAppend
        cases hAppend

/- A successful explicit function append is append-only. -/
theorem appendFunction?_appendOnly
    (env new : NameEnv A F)
    (function : F)
    (name : String)
    (hAppend : env.appendFunction? function name = some new) :
    AppendOnly env new := by
  cases hLookup : env.funName? function with
  | none =>
      by_cases hUsed : containsString env.usedNames name = true
      · simp only [appendFunction?, hLookup, hUsed, ↓reduceIte]
          at hAppend
        cases hAppend
      · simp only [appendFunction?, hLookup, hUsed]
          at hAppend
        cases hAppend
        exact ⟨⟨[], by simp⟩, List.prefix_append _ _⟩
  | some old =>
      by_cases hSame : old = name
      · simp only [appendFunction?, hLookup, hSame, ↓reduceIte]
          at hAppend
        cases hAppend
        exact AppendOnly.refl env
      · simp only [appendFunction?, hLookup, hSame, ↓reduceIte]
          at hAppend
        cases hAppend

private theorem appendRelationBindings?_appendOnly
    (env new : NameEnv A F)
    (bindings : List (A × String))
    (hAppend : env.appendRelationBindings? bindings = some new) :
    AppendOnly env new := by
  induction bindings generalizing env new with
  | nil =>
      simp only [appendRelationBindings?] at hAppend
      cases hAppend
      exact AppendOnly.refl _
  | cons binding bindings ih =>
      simp only [appendRelationBindings?] at hAppend
      cases hStep : env.appendRelation?
          binding.1 binding.2 with
      | none => simp [hStep] at hAppend
      | some next =>
          have hFirst := appendRelation?_appendOnly
            env next binding.1 binding.2 hStep
          have hRest : AppendOnly next new := by
            apply ih next
            simpa [hStep] using hAppend
          exact hFirst.trans hRest

private theorem appendFunctionBindings?_appendOnly
    (env new : NameEnv A F)
    (bindings : List (F × String))
    (hAppend : env.appendFunctionBindings? bindings = some new) :
    AppendOnly env new := by
  induction bindings generalizing env new with
  | nil =>
      simp only [appendFunctionBindings?] at hAppend
      cases hAppend
      exact AppendOnly.refl _
  | cons binding bindings ih =>
      simp only [appendFunctionBindings?] at hAppend
      cases hStep : env.appendFunction?
          binding.1 binding.2 with
      | none => simp [hStep] at hAppend
      | some next =>
          have hFirst := appendFunction?_appendOnly
            env next binding.1 binding.2 hStep
          have hRest : AppendOnly next new := by
            apply ih next
            simpa [hStep] using hAppend
          exact hFirst.trans hRest

/- Every successful explicit binding update is append-only. -/
theorem appendBindings?_appendOnly
    (env new : NameEnv A F)
    (relations : List (A × String))
    (functions : List (F × String))
    (hAppend :
      env.appendBindings? relations functions = some new) :
    AppendOnly env new := by
  unfold appendBindings? at hAppend
  cases hRelations : env.appendRelationBindings? relations with
  | none => simp [hRelations] at hAppend
  | some withRelations =>
      have hFirst := appendRelationBindings?_appendOnly
        env withRelations relations hRelations
      have hSecond : AppendOnly withRelations new := by
        apply appendFunctionBindings?_appendOnly
          withRelations new functions
        simpa [hRelations] using hAppend
      exact hFirst.trans hSecond

/- Append-only extension preserves a successful relation lookup. -/
theorem rel?_eq_some_of_appendOnly
    {old new : NameEnv A F}
    (h : AppendOnly old new)
    {r : A}
    {name : String}
    (hName : old.rel? r = some name) :
    new.rel? r = some name := by
  unfold rel? at hName ⊢
  cases hFind : old.relNames.find?
      (fun p => decide (p.1 = r)) with
  | none => simp [hFind] at hName
  | some p =>
      have hExtended := h.1.find?_eq_some hFind
      simpa [hFind, hExtended] using hName

/- Append-only extension preserves a successful function lookup. -/
theorem funName?_eq_some_of_appendOnly
    {old new : NameEnv A F}
    (h : AppendOnly old new)
    {f : F}
    {name : String}
    (hName : old.funName? f = some name) :
    new.funName? f = some name := by
  unfold funName? at hName ⊢
  cases hFind : old.funNames.find?
      (fun p => decide (p.1 = f)) with
  | none => simp [hFind] at hName
  | some p =>
      have hExtended := h.2.find?_eq_some hFind
      simpa [hFind, hExtended] using hName

/- Build a name environment from one FOL formula. -/
def ofFormula
    [SolverName A]
    [SolverName F]
    (φ : FOL.Formula Λ) :
    NameEnv A F where
  relNames := assignSolverNames (formulaRelations φ)
  funNames := assignSolverNames (formulaFunctions φ)

/- Build a name environment from closed FOL sentences. -/
def ofSentences
    [SolverName A]
    [SolverName F]
    (φs : List (FOL.Sentence Λ)) :
    NameEnv A F where
  relNames :=
    assignSolverNames
      (φs.foldl (fun acc φ => acc ++ formulaRelations φ.1) [])
  funNames :=
    assignSolverNames
      (φs.foldl (fun acc φ => acc ++ formulaFunctions φ.1) [])

/- Build a name environment from one entailment. -/
def ofEntailment
    [SolverName A]
    [SolverName F]
    (E : FOL.SentenceEntailment Λ) :
    NameEnv A F :=
  ofSentences (E.axioms ++ [E.conjecture])

/-
  An environment built from a lawful pair of carriers is
  always well formed: distinct symbols get distinct names,
  every name is legal, and the two carriers share none.
-/
theorem wellFormed_ofSentences
    [SolverName A]
    [SolverName F]
    [LawfulSolverName A]
    [LawfulSolverName F]
    (hDisjoint : ∀ (r : A) (f : F), solverName r ≠ solverName f)
    (φs : List (FOL.Sentence Λ)) :
    (ofSentences (Λ := Λ) φs).wellFormed = true := by
  have hRelations := all_legalTptpName_assignSolverNames
    (φs.foldl (fun acc φ => acc ++ formulaRelations φ.1) [])
  have hFunctions := all_legalTptpName_assignSolverNames
    (φs.foldl (fun acc φ => acc ++ formulaFunctions φ.1) [])
  have hDisjointNames :
      ∀ left ∈ (ofSentences (Λ := Λ) φs).relNames.map Prod.snd,
        ∀ right ∈
          (ofSentences (Λ := Λ) φs).funNames.map Prod.snd,
          left ≠ right := by
    intro left hRelation right hFunction hEq
    obtain ⟨r, hRel⟩ :=
      exists_of_mem_map_snd_assignSolverNames hRelation
    obtain ⟨f, hFun⟩ :=
      exists_of_mem_map_snd_assignSolverNames hFunction
    exact hDisjoint r f (hRel.trans (hEq.trans hFun.symm))
  simp only [wellFormed, usedNames, List.all_append,
    Bool.and_eq_true, decide_eq_true_eq, List.nodup_append]
  exact ⟨⟨hRelations, hFunctions⟩,
    nodup_map_snd_assignSolverNames _,
    nodup_map_snd_assignSolverNames _, hDisjointNames⟩

/- The same for the environment of one entailment. -/
theorem wellFormed_ofEntailment
    [SolverName A]
    [SolverName F]
    [LawfulSolverName A]
    [LawfulSolverName F]
    (hDisjoint : ∀ (r : A) (f : F), solverName r ≠ solverName f)
    (E : FOL.SentenceEntailment Λ) :
    (ofEntailment E).wellFormed = true :=
  wellFormed_ofSentences hDisjoint _

/-
  Relation lookup. A symbol the environment never declared
  falls back to its carrier's own name, the same name a
  production carrier's builders assign. An explicit binding
  takes priority over that fallback, and on the legacy
  encoding-worker path such a binding is Rust's own proposal,
  not checked against this carrier's name (see
  `SolverName/Concrete.lean`'s comment on
  `solverNameIndexAlphaName`), so the solver need not see
  this spelling there.
-/
def rel
    [SolverName A]
    (env : NameEnv A F)
    (r : A) :
    String :=
  match env.relNames.find? (fun p => decide (p.1 = r)) with
  | some p => p.2
  | none => solverName r

/- Function lookup, with the carrier's name as fallback. -/
def funNameOf
    [SolverName F]
    (env : NameEnv A F)
    (f : F) :
    String :=
  match env.funNames.find? (fun p => decide (p.1 = f)) with
  | some p => p.2
  | none => solverName f

/- Human-readable source-to-TPTP symbol map. -/
def symbolMapComment
    (env : NameEnv A F)
    (funLabel : String := "function") :
    String :=
  let relLines :=
    env.relNames.map
      (fun p => "% relation " ++ reprStr p.1 ++ " -> " ++ p.2)
  let funLines :=
    env.funNames.map
      (fun p => "% " ++ funLabel ++ " " ++ reprStr p.1 ++ " -> " ++ p.2)
  let lines := relLines ++ funLines
  joinSep "\n"
    ("% TPTP symbol map:" ::
      if lines.isEmpty then ["% (none)"] else lines)

end NameEnv

end TPTP
end Vampire
end Whiel

------------------------------------------------------------
-- Term And Formula Rendering
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace TPTP

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/- Parenthesize a formula. -/
def paren
    (s : String) : String :=
  "(" ++ s ++ ")"

mutual
/- Print a term in TPTP FOF syntax using a name environment. -/
  def termWithEnv
      [SolverName F]
      (env : NameEnv A F) :
      FOL.Term Λ → String
  | .var x => varName x
  | .func f args =>
      let rendered := termListWithEnv env args
      match rendered with
      | [] => env.funNameOf f.1
      | _ =>
          env.funNameOf f.1 ++ "(" ++ joinSep "," rendered ++ ")"

/- Print a term list in TPTP FOF syntax using a name environment. -/
  def termListWithEnv
      [SolverName F]
      (env : NameEnv A F) :
      {n : Nat} → FOL.TermList Λ n → List String
  | _, .nil => []
  | _, .cons t ts =>
      termWithEnv env t :: termListWithEnv env ts
end

mutual
/- Strictly render a term under an explicit name environment. -/
  def termWithEnv?
      (env : NameEnv A F) :
      FOL.Term Λ → Option String
  | .var x => some (varName x)
  | .func f args => do
      let name ← env.funName? f.1
      let rendered ← termListWithEnv? env args
      return match rendered with
        | [] => name
        | _ => name ++ "(" ++ joinSep "," rendered ++ ")"

/- Strictly render a term list under an explicit environment. -/
  def termListWithEnv?
      (env : NameEnv A F) :
      {n : Nat} → FOL.TermList Λ n → Option (List String)
  | _, .nil => some []
  | _, .cons t ts => do
      let head ← termWithEnv? env t
      let tail ← termListWithEnv? env ts
      return head :: tail
end

mutual
/- Print a term in TPTP FOF syntax. -/
  def term
      [SolverName F] :
      FOL.Term Λ → String
  | t =>
      let env : NameEnv A F :=
        { relNames := []
          funNames := assignSolverNames (termFunctions t) }
      termWithEnv env t

/- Print a term list in TPTP FOF syntax. -/
  def termList
      [SolverName F] :
      {n : Nat} → FOL.TermList Λ n → List String
  | _, .nil => []
  | _, .cons t ts => term t :: termList ts
end

/- Print a quantifier with the usual empty-list shortcut. -/
def quant
    (q : String)
    (xs : List Var)
    (body : String) : String :=
  match xs with
  | [] => body
  | _ =>
      q ++ " [" ++
        joinSep "," (xs.map varName) ++
        "] : " ++ paren body

/- Print a formula in TPTP FOF syntax using a name environment. -/
def formulaWithEnv
    [SolverName A]
    [SolverName F]
    (env : NameEnv A F) :
    FOL.Formula Λ → String
| .top => "$true"
| .bot => "$false"
| .eq t u =>
    paren (termWithEnv env t ++ " = " ++ termWithEnv env u)
| .rel r ts =>
    let rendered := termListWithEnv env ts
    match rendered with
    | [] => env.rel r.1
    | _ =>
        env.rel r.1 ++ "(" ++ joinSep "," rendered ++ ")"
| .and φ ψ =>
    paren (formulaWithEnv env φ ++ " & " ++ formulaWithEnv env ψ)
| .or φ ψ =>
    paren (formulaWithEnv env φ ++ " | " ++ formulaWithEnv env ψ)
| .not φ =>
    paren ("~ " ++ formulaWithEnv env φ)
| .imp φ ψ =>
    paren (formulaWithEnv env φ ++ " => " ++ formulaWithEnv env ψ)
| .iff φ ψ =>
    paren (formulaWithEnv env φ ++ " <=> " ++ formulaWithEnv env ψ)
| .forall_ x φ =>
    quant "!" [x] (formulaWithEnv env φ)
| .exists_ x φ =>
    quant "?" [x] (formulaWithEnv env φ)

/- Strictly render a formula under an explicit name environment. -/
def formulaWithEnv?
    (env : NameEnv A F) :
    FOL.Formula Λ → Option String
| .top => some "$true"
| .bot => some "$false"
| .eq t u => do
    let left ← termWithEnv? env t
    let right ← termWithEnv? env u
    return paren (left ++ " = " ++ right)
| .rel r ts => do
    let name ← env.rel? r.1
    let rendered ← termListWithEnv? env ts
    return match rendered with
      | [] => name
      | _ => name ++ "(" ++ joinSep "," rendered ++ ")"
| .and φ ψ => do
    let left ← formulaWithEnv? env φ
    let right ← formulaWithEnv? env ψ
    return paren (left ++ " & " ++ right)
| .or φ ψ => do
    let left ← formulaWithEnv? env φ
    let right ← formulaWithEnv? env ψ
    return paren (left ++ " | " ++ right)
| .not φ => do
    let body ← formulaWithEnv? env φ
    return paren ("~ " ++ body)
| .imp φ ψ => do
    let left ← formulaWithEnv? env φ
    let right ← formulaWithEnv? env ψ
    return paren (left ++ " => " ++ right)
| .iff φ ψ => do
    let left ← formulaWithEnv? env φ
    let right ← formulaWithEnv? env ψ
    return paren (left ++ " <=> " ++ right)
| .forall_ x φ => do
    let body ← formulaWithEnv? env φ
    return quant "!" [x] body
| .exists_ x φ => do
    let body ← formulaWithEnv? env φ
    return quant "?" [x] body

/- Print a formula in TPTP FOF syntax. -/
def formula
    [SolverName A]
    [SolverName F]
    (φ : FOL.Formula Λ) :
    String :=
  formulaWithEnv (NameEnv.ofFormula φ) φ

/- Print a closed FOL sentence using a name environment. -/
def sentenceWithEnv
    [SolverName A]
    [SolverName F]
    (env : NameEnv A F)
    (φ : FOL.Sentence Λ) : String :=
  formulaWithEnv env φ.1

/- Strictly render a closed sentence with an explicit environment. -/
def sentenceWithEnv?
    (env : NameEnv A F)
    (φ : FOL.Sentence Λ) : Option String :=
  formulaWithEnv? env φ.1

/- Print a closed FOL sentence. -/
def sentence
    [SolverName A]
    [SolverName F]
    (φ : FOL.Sentence Λ) : String :=
  sentenceWithEnv (NameEnv.ofSentences [φ]) φ

end TPTP
end Vampire
end Whiel

------------------------------------------------------------
-- FOF Declarations
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace TPTP

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/- One `fof` declaration. -/
def fof
    (name role body : String) : String :=
  "fof(" ++ name ++ ", " ++ role ++ ", " ++
    body ++ ")."

/- Enumerate strings with natural indexes. -/
def enumWith
    (namePrefix role : String)
    (fs : List String) : List String :=
  fs.zipIdx.map
    (fun p => fof (namePrefix ++ reprStr p.2) role p.1)

/- Render closed sentences as named axiom declarations. -/
def namedAxiomsWithEnv
    [SolverName A]
    [SolverName F]
    (env : NameEnv A F)
    (namePrefix : String)
    (φs : List (FOL.Sentence Λ)) :
    List String :=
  enumWith namePrefix "axiom" (φs.map (sentenceWithEnv env))

/- Render closed sentences as named axiom declarations. -/
def namedAxioms
    [SolverName A]
    [SolverName F]
    (namePrefix : String)
    (φs : List (FOL.Sentence Λ)) :
    List String :=
  namedAxiomsWithEnv (NameEnv.ofSentences φs) namePrefix φs

/- Render one closed sentence as a conjecture declaration. -/
def namedConjectureWithEnv
    [SolverName A]
    [SolverName F]
    (env : NameEnv A F)
    (name : String)
    (φ : FOL.Sentence Λ) :
    String :=
  fof name "conjecture" (sentenceWithEnv env φ)

/- Render one closed sentence as a conjecture declaration. -/
def namedConjecture
    [SolverName A]
    [SolverName F]
    (name : String)
    (φ : FOL.Sentence Λ) :
    String :=
  namedConjectureWithEnv (NameEnv.ofSentences [φ]) name φ

end TPTP
end Vampire
end Whiel

------------------------------------------------------------
-- FOL Entailment Rendering
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace TPTP

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/- Generic axiom block for a closed FOL entailment. -/
def axiomBlock
    [SolverName A]
    [SolverName F]
    (E : FOL.SentenceEntailment Λ) :
    String :=
  let env := NameEnv.ofEntailment E
  joinSep "\n"
    (env.symbolMapComment ::
      namedAxiomsWithEnv env "ax_" E.axioms)

/- Generic conjecture declaration for a FOL entailment. -/
def conjectureDecl
    [SolverName A]
    [SolverName F]
    (E : FOL.SentenceEntailment Λ) :
    String :=
  let env := NameEnv.ofEntailment E
  namedConjectureWithEnv env "conjecture" E.conjecture

/- Generic full TPTP problem for a closed FOL entailment. -/
def problem
    [SolverName A]
    [SolverName F]
    (E : FOL.SentenceEntailment Λ) :
    String :=
  if E.axioms.isEmpty then
    conjectureDecl E ++ "\n"
  else
    axiomBlock E ++ "\n" ++ conjectureDecl E ++ "\n"

end TPTP
end Vampire
end Whiel

------------------------------------------------------------
-- RelCalc Entailment Rendering With Provenance
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace TPTP

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Axioms used by the RelCalc-to-FOL translation. -/
def relCalcAxioms
    [LinearOrder A]
    [LinearOrder D]
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    List (FOL.Sentence (Γ.toFOLSignature E.constants)) :=
  [RelCalc.ToFOL.activeDomainSentence Γ E.constants] ++
    RelCalc.ToFOL.constantDistinctSentences
      (Γ := Γ) E.constants ++
      E.toFOLSourceAxioms

/- Name environment used by one RelCalc entailment. -/
def relCalcNameEnv
    [SolverName A]
    [SolverName D]
    [LinearOrder A]
    [LinearOrder D]
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    NameEnv A D :=
  NameEnv.ofSentences
    (relCalcAxioms E ++ [E.toFOLSourceConjecture])

/-
  Axiom block for the RelCalc-to-FOL translation. This keeps
  support axiom provenance visible in the generated TPTP.
-/
def relCalcAxiomBlock
    [SolverName A]
    [SolverName D]
    [LinearOrder A]
    [LinearOrder D]
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    String :=
  let env := relCalcNameEnv E
  let adom :=
    fof "adom_ax" "axiom"
      (sentenceWithEnv env
        (RelCalc.ToFOL.activeDomainSentence Γ E.constants))
  let cons :=
    namedAxiomsWithEnv env "cons_ax_"
      (RelCalc.ToFOL.constantDistinctSentences
        (Γ := Γ) E.constants)
  let source := namedAxiomsWithEnv env "source_ax_" E.toFOLSourceAxioms
  joinSep "\n"
    ([env.symbolMapComment (funLabel := "constant"), adom] ++
      cons ++ source)

/- Conjecture declaration for the RelCalc translation. -/
def relCalcConjectureDecl
    [SolverName A]
    [SolverName D]
    [LinearOrder A]
    [LinearOrder D]
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    String :=
  namedConjectureWithEnv
    (relCalcNameEnv E) "conjecture" E.toFOLSourceConjecture

/- Full TPTP problem for a RelCalc entailment. -/
def relCalcProblem
    [SolverName A]
    [SolverName D]
    [LinearOrder A]
    [LinearOrder D]
    (E : RelCalc.SentenceEntailment (D := D) Γ) :
    String :=
  relCalcAxiomBlock E ++ "\n" ++
    relCalcConjectureDecl E ++ "\n"

end TPTP
end Vampire
end Whiel
