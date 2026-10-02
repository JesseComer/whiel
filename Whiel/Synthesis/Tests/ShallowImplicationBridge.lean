-- Author: Jesse Comer
import Databases.Core.Notation
import Databases.FOL.ShallowSemantics

/-
  Focused checks for the closed-implication bridge used by
  generated Vampire proof reconstruction.

  The test signature includes nullary through ternary
  relations and nullary through binary functions. Its raw
  proof has the same polymorphic shape as leancheck output.
-/

------------------------------------------------------------
-- Test Signature
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ShallowImplicationBridge

inductive Rel
| flag
| edge
| cube
deriving DecidableEq, Repr

instance : RelationNames Rel where
  decEq := inferInstance
  repr := inferInstance

inductive Fun
| constant
| next
| pair
deriving DecidableEq, Repr

instance : FunctionNames Fun where
  decEq := inferInstance
  repr := inferInstance

def Λ : Signature Rel Fun :=
  sig![
    rels:
      Rel.flag (arity: 0),
      Rel.edge (arity: 2),
      Rel.cube (arity: 3)
    funs:
      Fun.constant (arity: 0),
      Fun.next (arity: 1),
      Fun.pair (arity: 2)
  ]

def flagSym : Signature.Rel Λ :=
  Λ.sym Rel.flag

def edgeSym : Signature.Rel Λ :=
  Λ.sym Rel.edge

def cubeSym : Signature.Rel Λ :=
  Λ.sym Rel.cube

def constantSym : Signature.Fun Λ :=
  Λ.func Fun.constant

def nextSym : Signature.Fun Λ :=
  Λ.func Fun.next

def pairSym : Signature.Fun Λ :=
  Λ.func Fun.pair

end ShallowImplicationBridge
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Test Entailment
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ShallowImplicationBridge

def constantTerm : FOL.Term Λ :=
  .func constantSym .nil

def nextTerm
    (t : FOL.Term Λ) :
    FOL.Term Λ :=
  .func nextSym (.cons t .nil)

def pairTerm
    (t u : FOL.Term Λ) :
    FOL.Term Λ :=
  .func pairSym (.cons t (.cons u .nil))

def flagFormula : FOL.Formula Λ :=
  .rel flagSym .nil

def edgeFormula
    (t u : FOL.Term Λ) :
    FOL.Formula Λ :=
  .rel edgeSym (.cons t (.cons u .nil))

def cubeFormula
    (t u v : FOL.Term Λ) :
    FOL.Formula Λ :=
  .rel cubeSym
    (.cons t (.cons u (.cons v .nil)))

def firstAxiom : FOL.Sentence Λ :=
  ⟨.forall_ 0
      (.imp
        (edgeFormula constantTerm (.var 0))
        flagFormula),
    by decide⟩

def secondAxiom : FOL.Sentence Λ :=
  ⟨.forall_ 0 (.forall_ 1
      (.imp
        (cubeFormula constantTerm
          (nextTerm (.var 0))
          (pairTerm (.var 0) (.var 1)))
        (edgeFormula constantTerm (.var 1)))),
    by decide⟩

def conjecture : FOL.Sentence Λ :=
  ⟨.forall_ 0 (.forall_ 1
      (.imp
        (cubeFormula constantTerm
          (nextTerm (.var 0))
          (pairTerm (.var 0) (.var 1)))
        flagFormula)),
    by decide⟩

def entailment : FOL.SentenceEntailment Λ where
  axioms := [firstAxiom, secondAxiom]
  conjecture := conjecture

def associationAxiom : FOL.Sentence Λ :=
  ⟨.and
      (.and flagFormula
        (edgeFormula constantTerm constantTerm))
      (cubeFormula constantTerm constantTerm
        constantTerm),
    by decide⟩

def associationConjecture : FOL.Sentence Λ :=
  ⟨.or
      (.or flagFormula
        (edgeFormula constantTerm constantTerm))
      (cubeFormula constantTerm constantTerm
        constantTerm),
    by decide⟩

def associationEntailment :
    FOL.SentenceEntailment Λ where
  axioms := [associationAxiom]
  conjecture := associationConjecture

end ShallowImplicationBridge
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Raw-Proof Reconstruction
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ShallowImplicationBridge

universe u

open FOL

theorem rawProof
    {ι : Type u}
    [Inhabited ι]
    {rFlag : Prop}
    {rEdge : ι → ι → Prop}
    {rCube : ι → ι → ι → Prop}
    {fConstant : ι}
    {fNext : ι → ι}
    {fPair : ι → ι → ι} :
    ((∀ x : ι, rEdge fConstant x → rFlag) ∧
      (∀ x y : ι,
        rCube fConstant (fNext x) (fPair x y) →
          rEdge fConstant y)) →
      ∀ x y : ι,
        rCube fConstant (fNext x) (fPair x y) →
          rFlag := by
  intro h x y hCube
  exact h.1 y (h.2 x y hCube)

theorem associationRawProof
    {ι : Type u}
    [Inhabited ι]
    {rFlag : Prop}
    {rEdge : ι → ι → Prop}
    {rCube : ι → ι → ι → Prop}
    {fConstant : ι} :
    (rFlag ∧ rEdge fConstant fConstant ∧
      rCube fConstant fConstant fConstant) →
    rFlag ∨ rEdge fConstant fConstant ∨
      rCube fConstant fConstant fConstant := by
  intro h
  exact Or.inl h.1

inductive Carrier
| point
deriving DecidableEq, Repr

instance : Inhabited Carrier where
  default := .point

instance : Domain Carrier where
  inhabited := inferInstance
  decEq := inferInstance
  repr := inferInstance

theorem entailmentValid :
    entailment.Valid (D := Carrier) := by
  apply
    SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ I _σ
  let rFlag : Prop := I.rels flagSym
  let rEdge : ι → ι → Prop := I.rels edgeSym
  let rCube : ι → ι → ι → Prop := I.rels cubeSym
  let fConstant : ι := I.funcs constantSym
  let fNext : ι → ι := I.funcs nextSym
  let fPair : ι → ι → ι := I.funcs pairSym
  change
    ((∀ x : ι, rEdge fConstant x → rFlag) ∧
      (∀ x y : ι,
        rCube fConstant (fNext x) (fPair x y) →
          rEdge fConstant y)) →
      ∀ x y : ι,
        rCube fConstant (fNext x) (fPair x y) →
          rFlag
  exact
    @rawProof ι inferInstance rFlag rEdge rCube
      fConstant fNext fPair

theorem associationEntailmentValid :
    associationEntailment.Valid (D := Carrier) := by
  apply
    SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ I _σ
  let rFlag : Prop := I.rels flagSym
  let rEdge : ι → ι → Prop := I.rels edgeSym
  let rCube : ι → ι → ι → Prop := I.rels cubeSym
  let fConstant : ι := I.funcs constantSym
  change
    ((rFlag ∧ rEdge fConstant fConstant) ∧
      rCube fConstant fConstant fConstant) →
    (rFlag ∨ rEdge fConstant fConstant) ∨
      rCube fConstant fConstant fConstant
  simpa only [and_assoc, or_assoc] using
    (@associationRawProof ι inferInstance rFlag
      rEdge rCube fConstant)

end ShallowImplicationBridge
end Tests
end Synthesis
end Whiel
