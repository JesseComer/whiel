-- Author: Jesse Comer
import Whiel.Vampire.TPTP

/-
  Stable role-neutral TPTP encoding.

  Theorems in this file connect one cached rendering to
  larger constant signatures and append-only name-environment
  extensions. They compare rendered strings rather than raw
  FOL terms, whose signature-indexed types differ.
-/

------------------------------------------------------------
-- Append-Only Rendering Stability
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace TPTP

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

mutual
/- A successful strict term rendering survives extension. -/
  theorem termWithEnv?_eq_some_of_appendOnly
      {old new : NameEnv A F}
      (hAppend : NameEnv.AppendOnly old new)
      (t : FOL.Term Λ)
      (body : String)
      (hBody : termWithEnv? old t = some body) :
      termWithEnv? new t = some body := by
    cases t with
    | var x =>
        simpa [termWithEnv?] using hBody
    | func f args =>
        cases hName : old.funName? f.1 with
        | none =>
            simp [termWithEnv?, hName] at hBody
        | some name =>
            have hNewName :=
              NameEnv.funName?_eq_some_of_appendOnly
                hAppend hName
            cases hArgs : termListWithEnv? old args with
            | none =>
                simp [termWithEnv?, hName, hArgs] at hBody
            | some rendered =>
                have hNewArgs :=
                  termListWithEnv?_eq_some_of_appendOnly
                    hAppend args rendered hArgs
                simpa [termWithEnv?, hName, hNewName,
                  hArgs, hNewArgs] using hBody

/- A successful strict term-list rendering survives extension. -/
  theorem termListWithEnv?_eq_some_of_appendOnly
      {old new : NameEnv A F}
      (hAppend : NameEnv.AppendOnly old new)
      {n : Nat}
      (ts : FOL.TermList Λ n)
      (bodies : List String)
      (hBodies : termListWithEnv? old ts = some bodies) :
      termListWithEnv? new ts = some bodies := by
    cases ts with
    | nil =>
        simpa [termListWithEnv?] using hBodies
    | cons t ts =>
        cases hHead : termWithEnv? old t with
        | none =>
            simp [termListWithEnv?, hHead] at hBodies
        | some head =>
            have hNewHead :=
              termWithEnv?_eq_some_of_appendOnly
                hAppend t head hHead
            cases hTail : termListWithEnv? old ts with
            | none =>
                simp [termListWithEnv?, hHead, hTail] at hBodies
            | some tail =>
                have hNewTail :=
                  termListWithEnv?_eq_some_of_appendOnly
                    hAppend ts tail hTail
                simpa [termListWithEnv?, hHead, hNewHead,
                  hTail, hNewTail] using hBodies
end

/- A successful strict formula rendering survives extension. -/
theorem formulaWithEnv?_eq_some_of_appendOnly
    {old new : NameEnv A F}
    (hAppend : NameEnv.AppendOnly old new)
    (φ : FOL.Formula Λ)
    (body : String)
    (hBody : formulaWithEnv? old φ = some body) :
    formulaWithEnv? new φ = some body := by
  induction φ generalizing body with
  | top =>
      simpa [formulaWithEnv?] using hBody
  | bot =>
      simpa [formulaWithEnv?] using hBody
  | eq t u =>
      cases hLeft : termWithEnv? old t with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          have hNewLeft :=
            termWithEnv?_eq_some_of_appendOnly
              hAppend t left hLeft
          cases hRight : termWithEnv? old u with
          | none =>
              simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hNewRight :=
                termWithEnv?_eq_some_of_appendOnly
                  hAppend u right hRight
              simpa [formulaWithEnv?, hLeft, hNewLeft,
                hRight, hNewRight] using hBody
  | rel r ts =>
      cases hName : old.rel? r.1 with
      | none => simp [formulaWithEnv?, hName] at hBody
      | some name =>
          have hNewName :=
            NameEnv.rel?_eq_some_of_appendOnly hAppend hName
          cases hArgs : termListWithEnv? old ts with
          | none => simp [formulaWithEnv?, hName, hArgs] at hBody
          | some rendered =>
              have hNewArgs :=
                termListWithEnv?_eq_some_of_appendOnly
                  hAppend ts rendered hArgs
              simpa [formulaWithEnv?, hName, hNewName,
                hArgs, hNewArgs] using hBody
  | and φ ψ ihφ ihψ =>
      cases hLeft : formulaWithEnv? old φ with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          have hNewLeft := ihφ left hLeft
          cases hRight : formulaWithEnv? old ψ with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hNewRight := ihψ right hRight
              simpa [formulaWithEnv?, hLeft, hNewLeft,
                hRight, hNewRight] using hBody
  | or φ ψ ihφ ihψ =>
      cases hLeft : formulaWithEnv? old φ with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          have hNewLeft := ihφ left hLeft
          cases hRight : formulaWithEnv? old ψ with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hNewRight := ihψ right hRight
              simpa [formulaWithEnv?, hLeft, hNewLeft,
                hRight, hNewRight] using hBody
  | not φ ih =>
      cases hInner : formulaWithEnv? old φ with
      | none => simp [formulaWithEnv?, hInner] at hBody
      | some inner =>
          have hNewInner := ih inner hInner
          simpa [formulaWithEnv?, hInner, hNewInner] using hBody
  | imp φ ψ ihφ ihψ =>
      cases hLeft : formulaWithEnv? old φ with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          have hNewLeft := ihφ left hLeft
          cases hRight : formulaWithEnv? old ψ with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hNewRight := ihψ right hRight
              simpa [formulaWithEnv?, hLeft, hNewLeft,
                hRight, hNewRight] using hBody
  | iff φ ψ ihφ ihψ =>
      cases hLeft : formulaWithEnv? old φ with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          have hNewLeft := ihφ left hLeft
          cases hRight : formulaWithEnv? old ψ with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hNewRight := ihψ right hRight
              simpa [formulaWithEnv?, hLeft, hNewLeft,
                hRight, hNewRight] using hBody
  | forall_ x φ ih =>
      cases hInner : formulaWithEnv? old φ with
      | none => simp [formulaWithEnv?, hInner] at hBody
      | some inner =>
          have hNewInner := ih inner hInner
          simpa [formulaWithEnv?, hInner, hNewInner] using hBody
  | exists_ x φ ih =>
      cases hInner : formulaWithEnv? old φ with
      | none => simp [formulaWithEnv?, hInner] at hBody
      | some inner =>
          have hNewInner := ih inner hInner
          simpa [formulaWithEnv?, hInner, hNewInner] using hBody

/- A successful strict sentence rendering survives extension. -/
theorem sentenceWithEnv?_eq_some_of_appendOnly
    {old new : NameEnv A F}
    (hAppend : NameEnv.AppendOnly old new)
    (φ : FOL.Sentence Λ)
    (body : String)
    (hBody : sentenceWithEnv? old φ = some body) :
    sentenceWithEnv? new φ = some body :=
  formulaWithEnv?_eq_some_of_appendOnly
    hAppend φ.1 body hBody

mutual
/- Strict and legacy term renderers agree on success. -/
  theorem termWithEnv_eq_of_strict
      [SolverName F]
      (env : NameEnv A F)
      (t : FOL.Term Λ)
      (body : String)
      (hBody : termWithEnv? env t = some body) :
      termWithEnv env t = body := by
    cases t with
    | var x => simpa [termWithEnv?, termWithEnv] using hBody
    | func f args =>
        cases hName : env.funName? f.1 with
        | none => simp [termWithEnv?, hName] at hBody
        | some name =>
            cases hArgs : termListWithEnv? env args with
            | none => simp [termWithEnv?, hName, hArgs] at hBody
            | some rendered =>
                have hLegacyName : env.funNameOf f.1 = name := by
                  unfold NameEnv.funName? at hName
                  unfold NameEnv.funNameOf
                  cases hFind : env.funNames.find?
                      (fun p => decide (p.1 = f.1)) with
                  | none => simp [hFind] at hName
                  | some p => simpa [hFind] using hName
                have hLegacyArgs :=
                  termListWithEnv_eq_of_strict
                    env args rendered hArgs
                simpa [termWithEnv?, termWithEnv, hName,
                  hArgs, hLegacyName, hLegacyArgs] using hBody

/- Strict and legacy term-list renderers agree on success. -/
  theorem termListWithEnv_eq_of_strict
      [SolverName F]
      (env : NameEnv A F)
      {n : Nat}
      (ts : FOL.TermList Λ n)
      (bodies : List String)
      (hBodies : termListWithEnv? env ts = some bodies) :
      termListWithEnv env ts = bodies := by
    cases ts with
    | nil => simpa [termListWithEnv?, termListWithEnv] using hBodies
    | cons t ts =>
        cases hHead : termWithEnv? env t with
        | none => simp [termListWithEnv?, hHead] at hBodies
        | some head =>
            cases hTail : termListWithEnv? env ts with
            | none =>
                simp [termListWithEnv?, hHead, hTail] at hBodies
            | some tail =>
                have hLegacyHead :=
                  termWithEnv_eq_of_strict env t head hHead
                have hLegacyTail :=
                  termListWithEnv_eq_of_strict env ts tail hTail
                simpa [termListWithEnv?, termListWithEnv,
                  hHead, hTail, hLegacyHead, hLegacyTail] using hBodies
end

/- Strict and legacy formula renderers agree on success. -/
theorem formulaWithEnv_eq_of_strict
    [SolverName A]
    [SolverName F]
    (env : NameEnv A F)
    (φ : FOL.Formula Λ)
    (body : String)
    (hBody : formulaWithEnv? env φ = some body) :
    formulaWithEnv env φ = body := by
  induction φ generalizing body with
  | top => simpa [formulaWithEnv?, formulaWithEnv] using hBody
  | bot => simpa [formulaWithEnv?, formulaWithEnv] using hBody
  | eq t u =>
      cases hLeft : termWithEnv? env t with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          cases hRight : termWithEnv? env u with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hLegacyLeft :=
                termWithEnv_eq_of_strict env t left hLeft
              have hLegacyRight :=
                termWithEnv_eq_of_strict env u right hRight
              simpa [formulaWithEnv?, formulaWithEnv,
                hLeft, hRight, hLegacyLeft, hLegacyRight] using hBody
  | rel r ts =>
      cases hName : env.rel? r.1 with
      | none => simp [formulaWithEnv?, hName] at hBody
      | some name =>
          cases hArgs : termListWithEnv? env ts with
          | none => simp [formulaWithEnv?, hName, hArgs] at hBody
          | some rendered =>
              have hLegacyName : env.rel r.1 = name := by
                unfold NameEnv.rel? at hName
                unfold NameEnv.rel
                cases hFind : env.relNames.find?
                    (fun p => decide (p.1 = r.1)) with
                | none => simp [hFind] at hName
                | some p => simpa [hFind] using hName
              have hLegacyArgs :=
                termListWithEnv_eq_of_strict
                  env ts rendered hArgs
              simpa [formulaWithEnv?, formulaWithEnv, hName,
                hArgs, hLegacyName, hLegacyArgs] using hBody
  | and φ ψ ihφ ihψ =>
      cases hLeft : formulaWithEnv? env φ with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          cases hRight : formulaWithEnv? env ψ with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hLegacyLeft := ihφ left hLeft
              have hLegacyRight := ihψ right hRight
              simpa [formulaWithEnv?, formulaWithEnv, hLeft,
                hRight, hLegacyLeft, hLegacyRight] using hBody
  | or φ ψ ihφ ihψ =>
      cases hLeft : formulaWithEnv? env φ with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          cases hRight : formulaWithEnv? env ψ with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hLegacyLeft := ihφ left hLeft
              have hLegacyRight := ihψ right hRight
              simpa [formulaWithEnv?, formulaWithEnv, hLeft,
                hRight, hLegacyLeft, hLegacyRight] using hBody
  | not φ ih =>
      cases hInner : formulaWithEnv? env φ with
      | none => simp [formulaWithEnv?, hInner] at hBody
      | some inner =>
          have hLegacyInner := ih inner hInner
          simpa [formulaWithEnv?, formulaWithEnv,
            hInner, hLegacyInner] using hBody
  | imp φ ψ ihφ ihψ =>
      cases hLeft : formulaWithEnv? env φ with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          cases hRight : formulaWithEnv? env ψ with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hLegacyLeft := ihφ left hLeft
              have hLegacyRight := ihψ right hRight
              simpa [formulaWithEnv?, formulaWithEnv, hLeft,
                hRight, hLegacyLeft, hLegacyRight] using hBody
  | iff φ ψ ihφ ihψ =>
      cases hLeft : formulaWithEnv? env φ with
      | none => simp [formulaWithEnv?, hLeft] at hBody
      | some left =>
          cases hRight : formulaWithEnv? env ψ with
          | none => simp [formulaWithEnv?, hLeft, hRight] at hBody
          | some right =>
              have hLegacyLeft := ihφ left hLeft
              have hLegacyRight := ihψ right hRight
              simpa [formulaWithEnv?, formulaWithEnv, hLeft,
                hRight, hLegacyLeft, hLegacyRight] using hBody
  | forall_ x φ ih =>
      cases hInner : formulaWithEnv? env φ with
      | none => simp [formulaWithEnv?, hInner] at hBody
      | some inner =>
          have hLegacyInner := ih inner hInner
          simpa [formulaWithEnv?, formulaWithEnv,
            hInner, hLegacyInner] using hBody
  | exists_ x φ ih =>
      cases hInner : formulaWithEnv? env φ with
      | none => simp [formulaWithEnv?, hInner] at hBody
      | some inner =>
          have hLegacyInner := ih inner hInner
          simpa [formulaWithEnv?, formulaWithEnv,
            hInner, hLegacyInner] using hBody

/- Strict and legacy sentence renderers agree on success. -/
theorem sentenceWithEnv_eq_of_strict
    [SolverName A]
    [SolverName F]
    (env : NameEnv A F)
    (φ : FOL.Sentence Λ)
    (body : String)
    (hBody : sentenceWithEnv? env φ = some body) :
    sentenceWithEnv env φ = body :=
  formulaWithEnv_eq_of_strict env φ.1 body hBody

end TPTP
end Vampire
end Whiel

------------------------------------------------------------
-- Constant-Signature Rendering Stability
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace TPTP

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Render a source RelCalc term without a target signature. -/
def relTermWithEnv
    [SolverName D]
    (env : NameEnv A D) :
    RelTerm D → String
| .var x => varName x
| .const d => env.funNameOf d

/- Render a source term vector without a target signature. -/
def relTermVectorWithEnv
    [SolverName D]
    (env : NameEnv A D)
    {n : Nat}
    (ts : Vector (RelTerm D) n) :
    List String :=
  List.ofFn (fun i => relTermWithEnv env (ts.get i))

/- Render a source RelCalc formula without a target signature. -/
def relFormulaWithEnv
    [SolverName A]
    [SolverName D]
    (env : NameEnv A D) :
    RelCalc.Formula D Γ → String
| .top => "$true"
| .bot => "$false"
| .eq t u =>
    paren (relTermWithEnv env t ++ " = " ++
      relTermWithEnv env u)
| .rel a =>
    let rendered := relTermVectorWithEnv env a.args
    match rendered with
    | [] => env.rel a.rel
    | _ => env.rel a.rel ++ "(" ++ joinSep "," rendered ++ ")"
| .and φ ψ =>
    paren (relFormulaWithEnv env φ ++ " & " ++
      relFormulaWithEnv env ψ)
| .or φ ψ =>
    paren (relFormulaWithEnv env φ ++ " | " ++
      relFormulaWithEnv env ψ)
| .not φ =>
    paren ("~ " ++ relFormulaWithEnv env φ)
| .imp φ ψ =>
    paren (relFormulaWithEnv env φ ++ " => " ++
      relFormulaWithEnv env ψ)
| .iff φ ψ =>
    paren (relFormulaWithEnv env φ ++ " <=> " ++
      relFormulaWithEnv env ψ)
| .forall_ x φ =>
    quant "!" [x] (relFormulaWithEnv env φ)
| .exists_ x φ =>
    quant "?" [x] (relFormulaWithEnv env φ)

/- Rendering `TermList.ofFn` renders the source function. -/
theorem termListWithEnv_ofFn
    [SolverName D]
    (env : NameEnv A D)
    {n : Nat}
    (f : Fin n → FOL.Term (Γ.toFOLSignature C)) :
    termListWithEnv env (FOL.TermList.ofFn f) =
      List.ofFn (fun i => termWithEnv env (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [FOL.TermList.ofFn, termListWithEnv,
        List.ofFn_succ]
      congr 1
      exact ih (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

/- Rendering one translated term is target-signature independent. -/
theorem termWithEnv_termWithConstants
    [SolverName D]
    (env : NameEnv A D)
    (C : Finset D)
    (t : RelTerm D)
    (hC : t.constants ⊆ C) :
    termWithEnv env
        (RelCalc.ToFOL.trTerm Γ C t hC) =
      relTermWithEnv env t := by
  cases t <;> rfl

/- Rendering a translated term vector is signature independent. -/
theorem termListWithEnv_termVectorWithConstants
    [SolverName D]
    (env : NameEnv A D)
    (C : Finset D)
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (hC : RelTerm.tupleConstants ts ⊆ C) :
    termListWithEnv env
        (RelCalc.ToFOL.trTermVector Γ C ts hC) =
      relTermVectorWithEnv env ts := by
  rw [RelCalc.ToFOL.trTermVector,
    termListWithEnv_ofFn]
  unfold relTermVectorWithEnv
  congr 1
  funext i
  exact termWithEnv_termWithConstants env C (ts.get i) _

/- Rendering a translated formula renders its source syntax. -/
theorem formulaWithEnv_toFOLWithConstants
    [SolverName A]
    [SolverName D]
    (env : NameEnv A D)
    (φ : RelCalc.Formula D Γ)
    (C : Finset D)
    (hC : φ.constants ⊆ C) :
    formulaWithEnv env (φ.toFOLWithConstants C hC) =
      relFormulaWithEnv env φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | eq t u =>
      simp only [RelCalc.Formula.toFOLWithConstants,
        RelCalc.ToFOL.trFormula, formulaWithEnv,
        relFormulaWithEnv]
      rw [termWithEnv_termWithConstants,
        termWithEnv_termWithConstants]
  | rel a =>
      have hArgConstants :
          RelTerm.tupleConstants a.args ⊆ C := by
          intro d hd
          exact hC (by
            simpa [RelCalc.Formula.constants,
              RelAtom.constants] using hd)
      have hTerms := termListWithEnv_termVectorWithConstants
        (Γ := Γ) env C a.args hArgConstants
      unfold RelCalc.Formula.toFOLWithConstants
      rw [RelCalc.ToFOL.trFormula]
      unfold formulaWithEnv relFormulaWithEnv
      have hTerms' :
          termListWithEnv env
              (RelCalc.ToFOL.trTermVector Γ C a.args
                hArgConstants) =
            relTermVectorWithEnv env a.args := by
        exact hTerms
      dsimp only
      exact congrArg
        (fun rendered =>
          match rendered with
          | [] => env.rel a.rel
          | _ =>
              env.rel a.rel ++ "(" ++
                joinSep "," rendered ++ ")")
        hTerms'
  | and φ ψ ihφ ihψ =>
      simp only [RelCalc.Formula.toFOLWithConstants,
        RelCalc.ToFOL.trFormula, formulaWithEnv,
        relFormulaWithEnv]
      have hLeft := ihφ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd)))
      have hRight := ihψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd)))
      rw [RelCalc.Formula.toFOLWithConstants] at hLeft hRight
      rw [hLeft, hRight]
  | or φ ψ ihφ ihψ =>
      simp only [RelCalc.Formula.toFOLWithConstants,
        RelCalc.ToFOL.trFormula, formulaWithEnv,
        relFormulaWithEnv]
      have hLeft := ihφ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd)))
      have hRight := ihψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd)))
      rw [RelCalc.Formula.toFOLWithConstants] at hLeft hRight
      rw [hLeft, hRight]
  | not φ ih =>
      simp only [RelCalc.Formula.toFOLWithConstants,
        RelCalc.ToFOL.trFormula, formulaWithEnv,
        relFormulaWithEnv]
      have hInner := ih (by exact hC)
      rw [RelCalc.Formula.toFOLWithConstants] at hInner
      rw [hInner]
  | imp φ ψ ihφ ihψ =>
      simp only [RelCalc.Formula.toFOLWithConstants,
        RelCalc.ToFOL.trFormula, formulaWithEnv,
        relFormulaWithEnv]
      have hLeft := ihφ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd)))
      have hRight := ihψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd)))
      rw [RelCalc.Formula.toFOLWithConstants] at hLeft hRight
      rw [hLeft, hRight]
  | iff φ ψ ihφ ihψ =>
      simp only [RelCalc.Formula.toFOLWithConstants,
        RelCalc.ToFOL.trFormula, formulaWithEnv,
        relFormulaWithEnv]
      have hLeft := ihφ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd)))
      have hRight := ihψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd)))
      rw [RelCalc.Formula.toFOLWithConstants] at hLeft hRight
      rw [hLeft, hRight]
  | forall_ x φ ih =>
      simp only [RelCalc.Formula.toFOLWithConstants,
        RelCalc.ToFOL.trFormula, formulaWithEnv,
        relFormulaWithEnv]
      have hInner := ih (by exact hC)
      rw [RelCalc.Formula.toFOLWithConstants] at hInner
      rw [hInner]
  | exists_ x φ ih =>
      simp only [RelCalc.Formula.toFOLWithConstants,
        RelCalc.ToFOL.trFormula, formulaWithEnv,
        relFormulaWithEnv]
      have hInner := ih (by exact hC)
      rw [RelCalc.Formula.toFOLWithConstants] at hInner
      rw [hInner]

/- Target-constant extension does not change a role-neutral body. -/
theorem sentenceWithEnv_toFOLWithConstants_stable
    [SolverName A]
    [SolverName D]
    (φ : RelCalc.Sentence D Γ)
    (C₁ C₂ : Finset D)
    (h₁ : φ.constants ⊆ C₁)
    (h₂ : φ.constants ⊆ C₂)
    (env : NameEnv A D) :
    sentenceWithEnv env
        (φ.toFOLWithConstants C₁ h₁) =
      sentenceWithEnv env
        (φ.toFOLWithConstants C₂ h₂) := by
  rw [RelCalc.Sentence.toFOLWithConstants,
    RelCalc.Sentence.toFOLWithConstants,
    sentenceWithEnv, sentenceWithEnv,
    formulaWithEnv_toFOLWithConstants,
    formulaWithEnv_toFOLWithConstants]

/-
  A cached exact-constant body remains valid after both a
  target-constant extension and an append-only environment
  extension.
-/
theorem roleNeutralBody_stable
    [SolverName A]
    [SolverName D]
    (φ : RelCalc.Sentence D Γ)
    (C : Finset D)
    (hC : φ.constants ⊆ C)
    (old new : NameEnv A D)
    (hAppend : NameEnv.AppendOnly old new)
    (body : String)
    (hBody :
      sentenceWithEnv? old
          (φ.toFOLWithConstants φ.constants subset_rfl) =
        some body) :
    sentenceWithEnv new
        (φ.toFOLWithConstants C hC) = body := by
  have hExtended :
      sentenceWithEnv? new
          (φ.toFOLWithConstants φ.constants subset_rfl) =
        some body :=
    sentenceWithEnv?_eq_some_of_appendOnly
      hAppend _ body hBody
  have hStrictAgrees :
      sentenceWithEnv new
          (φ.toFOLWithConstants φ.constants subset_rfl) =
        body := by
    exact sentenceWithEnv_eq_of_strict
      new _ body hExtended
  rw [← sentenceWithEnv_toFOLWithConstants_stable
    φ φ.constants C subset_rfl hC new]
  exact hStrictAgrees

/- Render cached sentences under one shared constant union. -/
def renderBodiesAtConstants
    [SolverName A]
    [SolverName D]
    (cached : List (RelCalc.Sentence D Γ × String))
    (C : Finset D)
    (env : NameEnv A D)
    (hConstants : ∀ item ∈ cached, item.1.constants ⊆ C) :
    List String :=
  match cached with
  | [] => []
  | head :: tail =>
      sentenceWithEnv env
          (head.1.toFOLWithConstants C
            (hConstants head (by simp))) ::
        renderBodiesAtConstants tail C env
          (fun item hItem =>
            hConstants item (by simp [hItem]))

/-
  A finite cache remains stable under one shared constant
  union and one append-only environment extension.
-/
theorem roleNeutralBodies_stable
    [SolverName A]
    [SolverName D]
    (cached : List (RelCalc.Sentence D Γ × String))
    (C : Finset D)
    (old new : NameEnv A D)
    (hAppend : NameEnv.AppendOnly old new)
    (hConstants : ∀ item ∈ cached, item.1.constants ⊆ C)
    (hBodies : ∀ item ∈ cached,
      sentenceWithEnv? old
          (item.1.toFOLWithConstants
            item.1.constants subset_rfl) =
        some item.2) :
    renderBodiesAtConstants cached C new hConstants =
      cached.map Prod.snd := by
  induction cached with
  | nil => rfl
  | cons head tail ih =>
      simp only [renderBodiesAtConstants, List.map_cons,
        List.cons.injEq]
      constructor
      · exact roleNeutralBody_stable
          head.1 C (hConstants head (by simp)) old new
          hAppend head.2 (hBodies head (by simp))
      · apply ih
        intro item hItem
        exact hBodies item (by simp [hItem])

end TPTP
end Vampire
end Whiel
