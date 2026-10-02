-- Author: Jesse Comer
import Mathlib.Data.List.Lex

/-
  Ordering utilities shared by Whiel's concrete carriers.

  Key declarations:
    * `Whiel.Concrete.charLexLt`
    * `Whiel.Concrete.stringLexLt`

  These instances order characters by their numeric code and
  strings lexicographically by their character lists. The
  concrete data domain and indexed relation names use these
  orders to get stable `LinearOrder` instances.
-/

namespace Whiel

namespace Concrete

instance invImageDecidableRel
    {α β : Type}
    {r : β → β → Prop}
    [DecidableRel r]
    (f : α → β) :
    DecidableRel (InvImage r f) := by
  intro x y
  unfold InvImage
  infer_instance

theorem invImage_isStrictTotalOrder
    {α β : Type}
    {r : β → β → Prop}
    [IsStrictTotalOrder β r]
    (f : α → β)
    (hf : Function.Injective f) :
    IsStrictTotalOrder α (InvImage r f) where
  trichotomous :=
    (InvImage.trichotomous (r := r) hf).trichotomous
  irrefl :=
    (InvImage.irrefl r f inferInstance).irrefl
  trans :=
    (InvImage.isTrans r f inferInstance).trans

/- Character order induced by Unicode scalar values. -/
def charLexLt : Char → Char → Prop :=
  InvImage (· < ·) Char.toNat

instance : DecidableRel charLexLt := by
  unfold charLexLt
  infer_instance

private theorem charToNat_injective :
    Function.Injective Char.toNat := by
  intro a b h
  rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b, h]

private instance charLexLt_isStrictTotalOrder :
    IsStrictTotalOrder Char charLexLt := by
  unfold charLexLt
  exact invImage_isStrictTotalOrder
    Char.toNat charToNat_injective

instance : LinearOrder Char :=
  linearOrderOfSTO charLexLt

/- Lexicographic string order induced by `charLexLt`. -/
def stringLexLt : String → String → Prop :=
  InvImage (List.Lex charLexLt) String.toList

instance : DecidableRel stringLexLt := by
  unfold stringLexLt
  infer_instance

private theorem stringToList_injective :
    Function.Injective String.toList := by
  intro a b h
  exact String.toList_injective h

private instance listCharLexLt_isStrictTotalOrder :
    IsStrictTotalOrder (List Char) (List.Lex charLexLt) :=
  { isStrictWeakOrder_of_isOrderConnected with }

instance stringLexLt_isStrictTotalOrder :
    IsStrictTotalOrder String stringLexLt := by
  unfold stringLexLt
  exact invImage_isStrictTotalOrder
    String.toList stringToList_injective

instance : LinearOrder String :=
  linearOrderOfSTO stringLexLt

end Concrete

end Whiel
