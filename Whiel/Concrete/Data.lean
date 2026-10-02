-- Author: Jesse Comer
import Databases.Core.Basic
import Databases.Core.Notation
import Whiel.Concrete.Order
import Mathlib.Data.Prod.Lex

/-
  Concrete database domain for Whiel examples and
  verification artifacts.

  Key declarations:
    * `Whiel.Concrete.Data`
    * `LinearOrder Whiel.Concrete.Data`
    * `Domain Whiel.Concrete.Data`

  Values are natural numbers, strings, and Booleans. The
  domain is intentionally concrete so generated and
  example-level Whiel programs can be evaluated.
-/

namespace Whiel

namespace Concrete

/-
  Concrete database values for Whiel-facing examples:
  natural numbers, strings, and Booleans.
-/
inductive Data where
| num : Nat → Data
| str : String → Data
| bool : Bool → Data
deriving DecidableEq, Hashable

/- Printable representation used by DBLib displays. -/
def Data.pretty : Data → String
| .num n => toString n
| .str s => reprStr s
| .bool b => toString b

instance : Repr Data where
  reprPrec d _ := d.pretty

namespace Data

/- Concrete order with `bool < num < str`. -/
def lexLt : Data → Data → Prop
| .bool b₁, .bool b₂ => b₁ < b₂
| .bool _, .num _ => True
| .bool _, .str _ => True
| .num _, .bool _ => False
| .num n₁, .num n₂ => n₁ < n₂
| .num _, .str _ => True
| .str _, .bool _ => False
| .str _, .num _ => False
| .str s₁, .str s₂ => stringLexLt s₁ s₂

private theorem bool_lt_irrefl
    (b : Bool) :
    ¬ b < b := by
  cases b <;> decide

private theorem bool_eq_of_not_lt
    (a b : Bool)
    (hab : ¬ a < b)
    (hba : ¬ b < a) :
    a = b := by
  cases a <;> cases b <;>
    first | rfl | contradiction

instance : DecidableRel lexLt := by
  intro a b
  cases a <;> cases b <;>
    unfold lexLt <;> infer_instance

private theorem lexLt_irrefl :
    Std.Irrefl lexLt where
  irrefl
  | .num n => Nat.lt_irrefl n
  | .str s => by
      change ¬ stringLexLt s s
      exact irrefl s
  | .bool b => bool_lt_irrefl b

private theorem lexLt_trans :
    IsTrans Data lexLt where
  trans
  | .num _, .num _, .num _, hab, hbc =>
      lt_trans hab hbc
  | .num _, .num _, .str _, _hab, _hbc =>
      trivial
  | .num _, .num _, .bool _, _hab, hbc =>
      False.elim hbc
  | .num _, .str _, .num _, _hab, hbc =>
      False.elim hbc
  | .num _, .str _, .str _, _hab, _hbc =>
      trivial
  | .num _, .str _, .bool _, _hab, hbc =>
      False.elim hbc
  | .num _, .bool _, _, hab, _hbc =>
      False.elim hab
  | .str _, .num _, _, hab, _hbc =>
      False.elim hab
  | .str _, .str _, .num _, _hab, hbc =>
      False.elim hbc
  | .str s₁, .str s₂, .str s₃, hab, hbc => by
      change stringLexLt s₁ s₃
      change stringLexLt s₁ s₂ at hab
      change stringLexLt s₂ s₃ at hbc
      exact IsTrans.trans _ _ _ hab hbc
  | .str _, .str _, .bool _, _hab, hbc =>
      False.elim hbc
  | .str _, .bool _, _, hab, _hbc =>
      False.elim hab
  | .bool _, .num _, .num _, _hab, _hbc =>
      trivial
  | .bool _, .num _, .str _, _hab, _hbc =>
      trivial
  | .bool _, .num _, .bool _, _hab, hbc =>
      False.elim hbc
  | .bool _, .str _, .num _, _hab, hbc =>
      False.elim hbc
  | .bool _, .str _, .str _, _hab, _hbc =>
      trivial
  | .bool _, .str _, .bool _, _hab, hbc =>
      False.elim hbc
  | .bool _, .bool _, .num _, _hab, _hbc =>
      trivial
  | .bool _, .bool _, .str _, _hab, _hbc =>
      trivial
  | .bool _, .bool _, .bool _, hab, hbc =>
      lt_trans hab hbc

private theorem lexLt_trichotomous :
    Std.Trichotomous lexLt where
  trichotomous
  | .num n₁, .num n₂, hab, hba => by
      change ¬ n₁ < n₂ at hab
      change ¬ n₂ < n₁ at hba
      exact
        congrArg Data.num
          (Nat.le_antisymm
            (Nat.le_of_not_gt hba)
            (Nat.le_of_not_gt hab))
  | .num _, .str _, hab, _hba =>
      False.elim (hab trivial)
  | .num _, .bool _, _hab, hba =>
      False.elim (hba trivial)
  | .str _, .num _, _hab, hba =>
      False.elim (hba trivial)
  | .str s₁, .str s₂, hab, hba => by
      change ¬ stringLexLt s₁ s₂ at hab
      change ¬ stringLexLt s₂ s₁ at hba
      exact
        congrArg Data.str
          (Std.Trichotomous.trichotomous s₁ s₂ hab hba)
  | .str _, .bool _, _hab, hba =>
      False.elim (hba trivial)
  | .bool _, .num _, hab, _hba =>
      False.elim (hab trivial)
  | .bool _, .str _, hab, _hba =>
      False.elim (hab trivial)
  | .bool b₁, .bool b₂, hab, hba =>
      congrArg Data.bool
        (bool_eq_of_not_lt b₁ b₂ hab hba)

private instance lexLt_isStrictTotalOrder :
    IsStrictTotalOrder Data lexLt where
  toTrichotomous := lexLt_trichotomous
  toIsStrictOrder := {
    toIrrefl := lexLt_irrefl
    toIsTrans := lexLt_trans
  }

instance : LinearOrder Data :=
  linearOrderOfSTO lexLt

end Data

instance : Inhabited Data where
  default := Data.str ""

instance : Domain Data where
  inhabited := inferInstance
  decEq := inferInstance
  repr := inferInstance

instance : Coe String Data where
  coe := Data.str

instance (n : Nat) : OfNat Data n where
  ofNat := Data.num n

instance : Coe Bool Data where
  coe := Data.bool

instance : DBLib.Notation.Literal String Data where
  toTarget := Data.str

instance : DBLib.Notation.Literal Nat Data where
  toTarget := Data.num

instance : DBLib.Notation.Literal Bool Data where
  toTarget := Data.bool

instance : DBLib.Notation.PrettyLiteral Data where
  pretty := Data.pretty

end Concrete

end Whiel
