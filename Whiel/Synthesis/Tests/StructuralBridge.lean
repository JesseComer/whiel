-- Author: Jesse Comer
import Whiel.Vampire.StructuralBridge
import Whiel.Synthesis.Tests.ShallowImplicationBridge

/-
  Focused checks for the proof-producing structural bridge
  used by generated Vampire reconstruction modules.
-/

------------------------------------------------------------
-- Propositional Structure
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace StructuralBridge

variable {A B C D E F : Prop}

theorem andAssociation
    (h : A ∧ B ∧ C ∧ D) :
    ((A ∧ B) ∧ C) ∧ D := by
  structural_exact h

theorem orAssociation
    (h : A ∨ B ∨ C ∨ D) :
    ((A ∨ B) ∨ C) ∨ D := by
  structural_exact h

theorem implicationAssociation
    (h : (A ∧ B ∧ C) → D ∨ E ∨ F) :
    ((A ∧ B) ∧ C) → (D ∨ E) ∨ F := by
  structural_exact h

theorem iffAssociation
    (h : (A ∧ B ∧ C) ↔ D ∨ E ∨ F) :
    ((A ∧ B) ∧ C) ↔ (D ∨ E) ∨ F := by
  structural_exact h

theorem suppliedAntecedents
    (h : (A ∧ B ∧ C) → D ∨ E ∨ F)
    (hA : A)
    (hB : B)
    (hC : C) :
    (D ∨ E) ∨ F := by
  structural_apply h with hA, hB, hC

end StructuralBridge
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Quantifiers and Function Atoms
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace StructuralBridge

theorem forallAssociation
    {α : Type}
    {P Q R : α → Prop}
    (f : α → α)
    (h : ∀ x, P (f x) ∧ Q x ∧ R (f (f x))) :
    ∀ x, (P (f x) ∧ Q x) ∧ R (f (f x)) := by
  structural_exact h

theorem existsAssociation
    {α : Type}
    {P : α → α → Prop}
    {Q R : α → Prop}
    (f : α → α)
    (g : α → α → α)
    (h : ∃ x,
      P (f x) (g x (f x)) ∧ Q x ∧ R (f x)) :
    ∃ x,
      (P (f x) (g x (f x)) ∧ Q x) ∧
        R (f x) := by
  structural_exact h

theorem suppliedEqualityOrientation
    {α : Type}
    {A : Prop}
    {a b : α}
    (h : a = b → A)
    (hEq : b = a) :
    A := by
  structural_apply_eq_symm h with hEq

/-
  A goal that mirrors an atomic equality of the source is
  closed by the equality-symmetry bridge.
-/
theorem mirroredEquality
    {α : Type}
    {a b : α}
    (h : a = b) :
    b = a := by
  structural_exact_eq_symm h

/-
  A negated equality is bridged contravariantly, so the mirrored
  atom sits on the hypothesis side and is repaired there.
-/
theorem mirroredNegatedEquality
    {α : Type}
    {a b : α}
    (h : ¬ (a = b)) :
    ¬ (b = a) := by
  structural_exact_eq_symm h

/-
  An equality that is not merely mirrored gets no repair: the
  source proof is passed through unchanged and the kernel
  rejects the declaration. The added permissiveness is exactly
  symmetry.
-/
/--
error: (kernel) declaration type mismatch, 'Whiel.Synthesis.Tests.StructuralBridge.unmirroredEquality' has type
  ∀ {α : Type} {a b : α} {c : α}, a = b → a = b
but it is expected to have type
  ∀ {α : Type} {a b c : α}, a = b → c = a
-/
#guard_msgs in
theorem unmirroredEquality
    {α : Type}
    {a b c : α}
    (h : a = b) :
    c = a := by
  structural_exact_eq_symm h

end StructuralBridge
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Shallow FOL Reconstruction
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace StructuralBridge

open FOL
open ShallowImplicationBridge

theorem associationEntailmentValidStructural :
    associationEntailment.Valid (D := Carrier) := by
  apply
    SentenceEntailment.valid_of_implicationShallowValid
  intro ι _ I _σ
  let rFlag : Prop := I.rels flagSym
  let rEdge : ι → ι → Prop := I.rels edgeSym
  let rCube : ι → ι → ι → Prop := I.rels cubeSym
  let fConstant : ι := I.funcs constantSym
  structural_exact
    (@associationRawProof ι inferInstance rFlag
      rEdge rCube fConstant)

theorem associationEntailmentValidStructuralApply :
    associationEntailment.Valid (D := Carrier) := by
  apply SentenceEntailment.valid_of_shallowValid
  intro ι _ I hAxioms _σ
  let rFlag : Prop := I.rels flagSym
  let rEdge : ι → ι → Prop := I.rels edgeSym
  let rCube : ι → ι → ι → Prop := I.rels cubeSym
  let fConstant : ι := I.funcs constantSym
  have hAxiom :=
    hAxioms associationAxiom
      (by simp [associationEntailment]) _σ
  structural_apply
    (@associationRawProof ι inferInstance rFlag
      rEdge rCube fConstant) with hAxiom

theorem entailmentValidStructural :
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
  structural_exact
    (@rawProof ι inferInstance rFlag rEdge rCube
      fConstant fNext fPair)

#print axioms associationEntailmentValidStructural
#print axioms associationEntailmentValidStructuralApply
#print axioms entailmentValidStructural

end StructuralBridge
end Tests
end Synthesis
end Whiel
