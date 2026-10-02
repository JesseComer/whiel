import Databases.Core.Notation
import Whiel.Library.FiniteOrder

------------------------------------------------------------
-- Concrete Finite-Order Library Audit
------------------------------------------------------------

namespace Whiel
namespace Library
namespace Tests
namespace FiniteOrder

open Whiel.Library.FiniteOrder

inductive RelationName where
  | edge
  | target
  | subset
deriving DecidableEq, Repr

instance : RelationNames RelationName where
  decEq := inferInstance
  repr := inferInstance

instance : Domain Nat where
  inhabited := inferInstance
  decEq := inferInstance
  repr := inferInstance

def Γ : UnnamedSchema RelationName :=
  sch![RelationName.edge (arity: 2),
    RelationName.target (arity: 2),
    RelationName.subset (arity: 1)]

def edge :
    BinaryRelation Γ where
  symbol := Γ.sym RelationName.edge
  arityTwo := by decide

def target :
    BinaryRelation Γ where
  symbol := Γ.sym RelationName.target
  arityTwo := by decide

example :
    (FV000001.sentence
      (D := Nat) edge target).AdomValid :=
  FV000001.adomValid edge target

example :
    (FV000002.sentence
      (D := Nat) edge).AdomValid :=
  FV000002.adomValid edge

example :
    FV000001.sentence (D := Nat) edge target =
      epsilonMaxBinaryDomainSentence edge target := by
  rfl

example :
    FV000002.sentence (D := Nat) edge =
      linearOrderMaxSentence edge := by
  rfl

------------------------------------------------------------
-- Fresh-Symbol Hypothesis Audit
------------------------------------------------------------

private def saturatedNullarySchema :
    UnnamedSchema RelationName where
  syms := {RelationName.edge, RelationName.target,
    RelationName.subset}
  arity := fun _ => 0

private def domainDependentFormula :
    RelCalc.Formula Nat saturatedNullarySchema :=
  .forall_ 0 (.eq (.var 0) (.const 0))

private def domainDependentSentence :
    RelCalc.Sentence Nat saturatedNullarySchema :=
  domainDependentFormula.toSentence (by decide)

example :
    ¬ ∃ X : RelationName,
      X ∉ saturatedNullarySchema.syms := by
  rintro ⟨X, hX⟩
  cases X <;> simp [saturatedNullarySchema] at hX

private theorem saturatedExtension_adom_empty
    {Δ : UnnamedSchema RelationName}
    (hExt : Δ.extensionOf saturatedNullarySchema)
    (J : Instance Nat Δ) :
    J.Adom = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  rw [Instance.in_Adom_iff_in_Relation] at hd
  rcases hd with ⟨X, t, _ht, hdt⟩
  have hOld : X.1 ∈ saturatedNullarySchema.syms := by
    cases X.1 <;> simp [saturatedNullarySchema]
  have hArity : Δ.arity X = 0 := by
    have hEq :=
      UnnamedSchema.arity_eq_of_extension_mem
        hExt X hOld
    simpa [saturatedNullarySchema] using hEq.symm
  have hList : t.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact
      (show t.toList.length = Δ.arity X from
        Vector.length_toList).trans hArity
  rw [hList] at hdt
  simp at hdt

private theorem domainDependentSentence_adomValid :
    domainDependentSentence.AdomValid := by
  intro Δ hExt J
  have hEmpty := saturatedExtension_adom_empty hExt J
  unfold RelCalc.Sentence.SatIn
  intro σ
  change Assign.MapsInto σ ∅ _ ∧
    (∀ d, d ∈ J.Adom ∪ {0} → d = 0)
  constructor
  · intro x hx
    simp at hx
  · intro d hd
    rw [hEmpty] at hd
    simpa using hd

example :
    ¬domainDependentSentence.DomainIndependent := by
  intro hDI
  let I : Instance Nat saturatedNullarySchema :=
    fun _ => ∅
  have hSupport :
      RelCalc.Adom.toSet
          domainDependentSentence.1 I ⊆
        Set.univ := by
    intro d _hd
    exact Set.mem_univ d
  have hLocal :
      domainDependentSentence.SatIn I
        (RelCalc.Adom.toSet
          domainDependentSentence.1 I) :=
    domainDependentSentence_adomValid.localAdomValid I
  have hFull :
      domainDependentSentence.SatIn I Set.univ :=
    (hDI I Set.univ hSupport).mp hLocal
  have hAt := hFull default
  change Assign.MapsInto default ∅ Set.univ ∧
    (∀ d, d ∈ Set.univ → d = 0) at hAt
  have hEq := hAt.2 1 (Set.mem_univ _)
  omega

end FiniteOrder
end Tests
end Library
end Whiel
