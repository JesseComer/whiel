import Databases.RelCalc.Valid
import Databases.RelCalc.TermSubstitution

/-
  This file defines two reviewed finite-order library
  entries over an arbitrary ambient RelCalc schema.

  Key definitions include:
    * `Whiel.Library.FiniteOrder.BinaryRelation`
    * `Whiel.Library.FiniteOrder.FV000001.sentence`
    * `Whiel.Library.FiniteOrder.FV000002.sentence`

  Their intended active-domain meanings are stated by each
  accession's `meaning` theorem. Certificate authority is
  provided by each accession's `adomValid` theorem.

  The complete RelCalc constructor tree for each entry is
  visible in its `sentence` definition. Other declarations
  are relation infrastructure or proof support.
-/

------------------------------------------------------------
-- Binary Relation Syntax
------------------------------------------------------------

namespace Whiel
namespace Library
namespace FiniteOrder

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- A checked binary symbol in an ambient RelCalc schema. -/
structure BinaryRelation
    (Γ : UnnamedSchema A) where
  symbol : Γ.syms
  arityTwo : Γ.arity symbol = 2

namespace BinaryRelation

/- The binary tuple with the checked target arity. -/
def pair
    (R : BinaryRelation Γ)
    (left right : D) :
    Tuple D (Γ.arity R.symbol) :=
  Vector.ofFn fun index =>
    Fin.cases left (fun _ => right)
      (Fin.cast R.arityTwo index)

/- The binary atom at two variables. -/
def atom
    (R : BinaryRelation Γ)
    (left right : Var) :
    RelCalc.Formula D Γ :=
  .rel
    { rel := R.symbol
      args := Vector.ofFn fun index =>
        Fin.cases (.var left) (fun _ => .var right)
          (Fin.cast R.arityTwo index) }

/- The semantic binary relation represented by a symbol. -/
def Holds
    (R : BinaryRelation Γ)
    (I : Instance D Γ)
    (left right : D) : Prop :=
  R.pair left right ∈ I R.symbol

/- The atom reads the two selected assignment values. -/
theorem arbitraryAssignSatIn_atom
    (R : BinaryRelation Γ)
    (I : Instance D Γ)
    (Q : Set D)
    (σ : Assign D)
    (left right : Var) :
    RelCalc.Formula.ArbitraryAssignSatIn Q I σ
        (R.atom left right) ↔
      R.Holds I (σ left) (σ right) := by
  unfold atom RelCalc.Formula.ArbitraryAssignSatIn
    RelAtom.Sat RelAtom.evalFact RelFact.Mem
    RelAtom.evalTuple RelTerm.evalVector Holds pair
  have hTuple :
      (Vector.ofFn fun i =>
          RelTerm.eval σ
            ((Vector.ofFn fun index =>
              Fin.cases (.var left)
                (fun _ => .var right)
                (Fin.cast R.arityTwo index)).get i)) =
        (Vector.ofFn fun index =>
          Fin.cases (σ left) (fun _ => σ right)
            (Fin.cast R.arityTwo index)) := by
    apply Vector.ext
    intro i hi
    have hCoordinate :
        ∀ j : Fin 2,
          RelTerm.eval σ
              (Fin.cases (.var left)
                (fun _ => .var right) j) =
            Fin.cases (σ left) (fun _ => σ right) j := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · have hk : k = 0 := Fin.eq_zero k
        subst hk
        rfl
    simpa [Vector.get, Vector.ofFn] using
      hCoordinate
        (Fin.cast R.arityTwo ⟨i, hi⟩)
  rw [hTuple]

@[simp] theorem mem_freeVars_atom_iff
    (R : BinaryRelation Γ)
    (left right free : Var) :
    free ∈ (R.atom (D := D) left right).freeVars ↔
      free = left ∨ free = right := by
  change free ∈ RelTerm.tupleVars _ ↔ _
  rw [RelTerm.mem_tupleVars_iff]
  constructor
  · rintro ⟨index, member⟩
    let coordinate : Fin 2 :=
      Fin.cast R.arityTwo index
    have coordinateMember :
        free ∈
          (Fin.cases (.var left)
            (fun _ => .var right) coordinate :
            RelTerm D).vars := by
      simpa [atom, coordinate, Vector.get,
        Vector.ofFn] using member
    revert coordinateMember
    refine Fin.cases ?_ (fun tail => ?_) coordinate
    · intro member
      exact Or.inl
        (Finset.mem_singleton.mp member)
    · have hTail : tail = 0 := Fin.eq_zero tail
      subst hTail
      intro member
      exact Or.inr
        (Finset.mem_singleton.mp member)
  · rintro (equal | equal)
    · let index : Fin (Γ.arity R.symbol) :=
        Fin.cast R.arityTwo.symm ⟨0, by decide⟩
      have hIndex :
          Fin.cast R.arityTwo index =
            (⟨0, by decide⟩ : Fin 2) := by
        apply Fin.ext
        rfl
      refine ⟨index, ?_⟩
      have hMember :
          free ∈ (RelTerm.var left : RelTerm D).vars := by
        simp [RelTerm.vars, equal]
      simpa [atom, Vector.get, Vector.ofFn, hIndex]
        using hMember
    · let index : Fin (Γ.arity R.symbol) :=
        Fin.cast R.arityTwo.symm ⟨1, by decide⟩
      have hIndex :
          Fin.cast R.arityTwo index =
            (⟨1, by decide⟩ : Fin 2) := by
        apply Fin.ext
        rfl
      refine ⟨index, ?_⟩
      have hMember :
          free ∈
            (RelTerm.var right : RelTerm D).vars := by
        simp [RelTerm.vars, equal]
      simpa [atom, Vector.get, Vector.ofFn, hIndex]
        using hMember

end BinaryRelation

end FiniteOrder
end Library
end Whiel

------------------------------------------------------------
-- Finite Maximal-Member Lemma
------------------------------------------------------------

namespace Whiel
namespace Library
namespace FiniteOrder

variable {α : Type}

/-
  A finite nonempty strict partial order has a
  maximal member.
-/
private theorem exists_maximal_mem
    (relation : α → α → Prop)
    (decideEquality : DecidableEq α)
    (decideRelation : DecidableRel relation)
    (elements : Finset α)
    (nonempty : elements.Nonempty)
    (irreflexive : ∀ x, ¬ relation x x)
    (transitive : ∀ x y z,
      relation x y → relation y z → relation x z) :
    ∃ maximal,
      maximal ∈ elements ∧
        ∀ other,
          other ∈ elements →
            ¬ relation maximal other := by
  letI : DecidableEq α := decideEquality
  letI : DecidableRel relation := decideRelation
  induction elements using Finset.induction_on with
  | empty =>
      exact False.elim
        (Finset.not_nonempty_empty nonempty)
  | @insert candidate rest fresh ih =>
      by_cases restNonempty : rest.Nonempty
      · rcases ih restNonempty with
          ⟨maximal, maximalIn, maximalProperty⟩
        by_cases rises : relation maximal candidate
        · refine ⟨candidate,
            Finset.mem_insert_self candidate rest, ?_⟩
          intro other otherIn candidateRises
          rcases Finset.mem_insert.mp otherIn with
            otherEq | otherInRest
          · subst other
            exact irreflexive candidate candidateRises
          · exact maximalProperty other otherInRest
              (transitive maximal candidate other
                rises candidateRises)
        · refine ⟨maximal,
            Finset.mem_insert_of_mem maximalIn, ?_⟩
          intro other otherIn maximalRises
          rcases Finset.mem_insert.mp otherIn with
            otherEq | otherInRest
          · subst other
            exact rises maximalRises
          · exact maximalProperty other otherInRest
              maximalRises
      · refine ⟨candidate,
          Finset.mem_insert_self candidate rest, ?_⟩
        intro other otherIn candidateRises
        rcases Finset.mem_insert.mp otherIn with
          otherEq | otherInRest
        · subst other
          exact irreflexive candidate candidateRises
        · exact False.elim
            (restNonempty ⟨other, otherInRest⟩)

end FiniteOrder
end Library
end Whiel

------------------------------------------------------------
-- Finite-Validity Entry FV000001
------------------------------------------------------------

namespace Whiel
namespace Library
namespace FiniteOrder

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

namespace FV000001

/-
  If `R` is a strict partial order on the active domain,
  every nonempty subset defined by `exists y, T(x, y)` has
  an `R`-maximal member.
-/
def sentence
    (R T : BinaryRelation Γ) :
    RelCalc.Sentence D Γ :=
  ⟨.imp
      (.and
        (.forall_ 0 (.not (R.atom 0 0)))
        (.and
          (.forall_ 0 <| .forall_ 1 <| .forall_ 2 <|
            .imp
              (.and (R.atom 0 1) (R.atom 1 2))
              (R.atom 0 2))
          (.exists_ 0 <| .exists_ 3 <|
            T.atom 0 3)))
      (.exists_ 0 <|
        .and
          (.exists_ 3 <| T.atom 0 3)
          (.forall_ 1 <|
            .imp
              (.exists_ 3 <| T.atom 1 3)
              (.not (R.atom 0 1)))), by
    unfold RelCalc.Formula.IsSentence
    ext free
    simp [RelCalc.Formula.freeVars]
    aesop⟩

/- Checked active-domain interpretation of `sentence`. -/
theorem meaning
    (R T : BinaryRelation Γ)
    (I : Instance D Γ) :
    let Q := RelCalc.Adom.toSet
      (sentence (D := D) R T).1 I
    (sentence (D := D) R T).SatIn I Q ↔
      ((∀ x ∈ Q, ¬ R.Holds I x x) ∧
        (∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q,
          R.Holds I x y ∧ R.Holds I y z →
            R.Holds I x z) ∧
        (∃ x ∈ Q, ∃ y ∈ Q, T.Holds I x y)) →
      ∃ maximal ∈ Q,
        (∃ target ∈ Q,
          T.Holds I maximal target) ∧
        ∀ other ∈ Q,
          (∃ target ∈ Q,
            T.Holds I other target) →
          ¬ R.Holds I maximal other := by
  dsimp only
  rw [RelCalc.Sentence.satIn_iff
    (sentence R T) I
    (RelCalc.Adom.toSet
      (sentence (D := D) R T).1 I)
    (fun _ => default)]
  have hClosed :
      (sentence (D := D) R T).1.freeVars = ∅ :=
    (sentence (D := D) R T).2
  unfold RelCalc.Formula.SatIn
  rw [hClosed]
  simp [sentence,
    RelCalc.Formula.ArbitraryAssignSatIn,
    BinaryRelation.arbitraryAssignSatIn_atom,
    Assign.update, Assign.MapsInto]

set_option linter.flexible false in
private theorem finiteExtensionValid
    (R T : BinaryRelation Γ) :
    (sentence (D := D) R T).FiniteExtensionValid := by
  intro I Q _hSupport
  rw [RelCalc.Sentence.satIn_iff
    (sentence R T) I
    (fun d => d ∈ Q) (fun _ => default)]
  simp [sentence, RelCalc.Formula.SatIn,
    RelCalc.Formula.ArbitraryAssignSatIn,
    BinaryRelation.arbitraryAssignSatIn_atom,
    Assign.update]
  constructor
  · intro free member
    have hClosed := (sentence (D := D) R T).2
    change free ∈
      (sentence (D := D) R T).1.freeVars at member
    rw [hClosed] at member
    simp at member
  · intro hIrreflexive hTransitive witness witnessIn
      outgoing outgoingIn hOutgoing
    let hasOutgoing : D → Prop := fun value =>
      ∃ target ∈ Q, T.Holds I value target
    letI : DecidablePred hasOutgoing := by
      intro value
      unfold hasOutgoing
      letI : DecidablePred
          (fun target => T.Holds I value target) := by
        intro target
        unfold BinaryRelation.Holds
        infer_instance
      exact decidable_of_iff
        (∃ target : {d // d ∈ Q},
          T.Holds I value target.1)
        ⟨
          fun ⟨target, hTarget⟩ =>
            ⟨target.1, target.2, hTarget⟩,
          fun ⟨target, hTarget, hHolds⟩ =>
            ⟨⟨target, hTarget⟩, hHolds⟩
        ⟩
    let elements : Finset D := Q.filter hasOutgoing
    let relation : D → D → Prop := fun left right =>
      left ∈ Q ∧ right ∈ Q ∧
        R.Holds I left right
    have hNonempty : elements.Nonempty := by
      refine ⟨witness, Finset.mem_filter.mpr ?_⟩
      exact ⟨witnessIn,
        ⟨outgoing, outgoingIn, hOutgoing⟩⟩
    have hIrrelation :
        ∀ value, ¬ relation value value := by
      intro value hRelation
      exact hIrreflexive value hRelation.1
        hRelation.2.2
    have hTransrelation :
        ∀ left middle right,
          relation left middle →
            relation middle right →
              relation left right := by
      intro left middle right hLeft hRight
      exact
        ⟨hLeft.1, hRight.2.1,
          hTransitive left hLeft.1 middle hLeft.2.1
            right hRight.2.1 hLeft.2.2
            hRight.2.2⟩
    letI : DecidableRel relation := by
      intro left right
      change Decidable
        (left ∈ Q ∧ right ∈ Q ∧
          R.Holds I left right)
      unfold BinaryRelation.Holds
      infer_instance
    rcases exists_maximal_mem relation
        (inferInstance : DecidableEq D)
        (inferInstance : DecidableRel relation)
        elements hNonempty hIrrelation hTransrelation with
      ⟨maximal, maximalIn, maximalProperty⟩
    have maximalData := Finset.mem_filter.mp maximalIn
    refine ⟨maximal, maximalData.1,
      maximalData.2, ?_⟩
    intro other otherIn otherWitness otherWitnessIn
      otherOutgoing rises
    apply maximalProperty other
    · exact Finset.mem_filter.mpr
        ⟨otherIn,
          ⟨otherWitness, otherWitnessIn,
            otherOutgoing⟩⟩
    · exact ⟨maximalData.1, otherIn, rises⟩

/- Active-domain validity used by certificate replay. -/
theorem adomValid
    (R T : BinaryRelation Γ) :
    (sentence (D := D) R T).AdomValid :=
  RelCalc.Sentence.adomValid_of_finiteExtensionValid
    (sentence R T) (finiteExtensionValid R T)

end FV000001

end FiniteOrder
end Library
end Whiel

------------------------------------------------------------
-- Finite-Validity Entry FV000002
------------------------------------------------------------

namespace Whiel
namespace Library
namespace FiniteOrder

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

namespace FV000002

/-
  If `R` is a nonempty strict linear order on the active
  domain, that domain has an `R`-greatest element.
-/
def sentence
    (R : BinaryRelation Γ) :
    RelCalc.Sentence D Γ :=
  ⟨.imp
      (.and
        (.exists_ 0 .top)
        (.and
          (.forall_ 0 (.not (R.atom 0 0)))
          (.and
            (.forall_ 0 <| .forall_ 1 <| .forall_ 2 <|
              .imp
                (.and (R.atom 0 1) (R.atom 1 2))
                (R.atom 0 2))
            (.forall_ 0 <| .forall_ 1 <|
              .or
                (.eq (.var 0) (.var 1))
                (.or (R.atom 0 1)
                  (R.atom 1 0))))))
      (.exists_ 0 <| .forall_ 1 <|
        .or
          (.eq (.var 1) (.var 0))
          (R.atom 1 0)), by
    unfold RelCalc.Formula.IsSentence
    ext free
    simp [RelCalc.Formula.freeVars, RelTerm.vars]
    aesop⟩

/- Checked active-domain interpretation of `sentence`. -/
theorem meaning
    (R : BinaryRelation Γ)
    (I : Instance D Γ) :
    let Q := RelCalc.Adom.toSet
      (sentence (D := D) R).1 I
    (sentence (D := D) R).SatIn I Q ↔
      ((∃ x, x ∈ Q) ∧
        (∀ x ∈ Q, ¬ R.Holds I x x) ∧
        (∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q,
          R.Holds I x y ∧ R.Holds I y z →
            R.Holds I x z) ∧
        (∀ x ∈ Q, ∀ y ∈ Q,
          x = y ∨ R.Holds I x y ∨
            R.Holds I y x)) →
      ∃ greatest ∈ Q,
        ∀ other ∈ Q,
          other = greatest ∨
            R.Holds I other greatest := by
  dsimp only
  rw [RelCalc.Sentence.satIn_iff
    (sentence R) I
    (RelCalc.Adom.toSet
      (sentence (D := D) R).1 I)
    (fun _ => default)]
  have hClosed :
      (sentence (D := D) R).1.freeVars = ∅ :=
    (sentence (D := D) R).2
  unfold RelCalc.Formula.SatIn
  rw [hClosed]
  simp [sentence,
    RelCalc.Formula.ArbitraryAssignSatIn,
    BinaryRelation.arbitraryAssignSatIn_atom,
    Assign.update, Assign.MapsInto, RelTerm.eval]

set_option linter.flexible false in
private theorem finiteExtensionValid
    (R : BinaryRelation Γ) :
    (sentence (D := D) R).FiniteExtensionValid := by
  intro I Q _hSupport
  rw [RelCalc.Sentence.satIn_iff
    (sentence R) I
    (fun d => d ∈ Q) (fun _ => default)]
  simp [sentence, RelCalc.Formula.SatIn,
    RelCalc.Formula.ArbitraryAssignSatIn,
    BinaryRelation.arbitraryAssignSatIn_atom,
    Assign.update, RelTerm.eval]
  constructor
  · intro free member
    have hClosed := (sentence (D := D) R).2
    change free ∈
      (sentence (D := D) R).1.freeVars at member
    rw [hClosed] at member
    simp at member
  · intro witness witnessIn hIrreflexive
      hTransitive hTotal
    let relation : D → D → Prop := fun left right =>
      left ∈ Q ∧ right ∈ Q ∧
        R.Holds I left right
    have hNonempty : Q.Nonempty :=
      ⟨witness, witnessIn⟩
    have hIrrelation :
        ∀ value, ¬ relation value value := by
      intro value hRelation
      exact hIrreflexive value hRelation.1
        hRelation.2.2
    have hTransrelation :
        ∀ left middle right,
          relation left middle →
            relation middle right →
              relation left right := by
      intro left middle right hLeft hRight
      exact
        ⟨hLeft.1, hRight.2.1,
          hTransitive left hLeft.1 middle hLeft.2.1
            right hRight.2.1 hLeft.2.2
            hRight.2.2⟩
    letI : DecidableRel relation := by
      intro left right
      change Decidable
        (left ∈ Q ∧ right ∈ Q ∧
          R.Holds I left right)
      unfold BinaryRelation.Holds
      infer_instance
    rcases exists_maximal_mem relation
        (inferInstance : DecidableEq D)
        (inferInstance : DecidableRel relation)
        Q hNonempty hIrrelation hTransrelation with
      ⟨maximal, maximalIn, maximalProperty⟩
    refine ⟨maximal, maximalIn, ?_⟩
    intro other otherIn
    rcases hTotal other otherIn maximal maximalIn with
      equal | rises | falls
    · exact Or.inl equal
    · exact Or.inr rises
    · exact False.elim <| maximalProperty other
        otherIn ⟨maximalIn, otherIn, falls⟩

/- Active-domain validity used by certificate replay. -/
theorem adomValid
    (R : BinaryRelation Γ) :
    (sentence (D := D) R).AdomValid :=
  RelCalc.Sentence.adomValid_of_finiteExtensionValid
    (sentence R) (finiteExtensionValid R)

end FV000002

end FiniteOrder
end Library
end Whiel

------------------------------------------------------------
-- Registry-V2 Compatibility Names
------------------------------------------------------------

namespace Whiel
namespace Library
namespace FiniteOrder

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Historical registry-v2 name for `FV000001.sentence`. -/
abbrev epsilonMaxBinaryDomainSentence
    (R T : BinaryRelation Γ) :
    RelCalc.Sentence D Γ :=
  FV000001.sentence R T

/- Historical registry-v2 authority for `FV000001`. -/
theorem epsilonMaxBinaryDomain_adomValid
    (R T : BinaryRelation Γ) :
    (epsilonMaxBinaryDomainSentence
      (D := D) R T).AdomValid :=
  FV000001.adomValid R T

/- Historical registry-v2 name for `FV000002.sentence`. -/
abbrev linearOrderMaxSentence
    (R : BinaryRelation Γ) :
    RelCalc.Sentence D Γ :=
  FV000002.sentence R

/-
  Historical registry-v2 authority for `FV000002`.
-/
theorem linearOrderMax_adomValid
    (R : BinaryRelation Γ) :
    (linearOrderMaxSentence (D := D) R).AdomValid :=
  FV000002.adomValid R

end FiniteOrder
end Library
end Whiel
