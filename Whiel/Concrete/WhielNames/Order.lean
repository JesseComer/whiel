-- Author: Jesse Comer
import Whiel.Concrete.WhielNames
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order

/-
  Structural orders for the fixed-ambient Whiel
  relation-name carrier.

  Program symbols precede auxiliary symbols, which precede
  flag symbols. Ordinary symbols precede prophecy symbols.
  Names within each family retain their base-name (or flag
  identity) and index order.
-/

------------------------------------------------------------
-- Program-Name Order
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace ProgramNames

/-
  Structural order key: family, then base or flag identity,
  then index.
-/
private def orderKey :
    ProgramNames →
      Nat ×ₗ ((AlphaString ×ₗ Nat) ⊕ₗ (Nat ×ₗ Nat))
| .programSymbol base index =>
    toLex (0, Sum.inlₗ (toLex (base, index)))
| .auxiliarySymbol base index =>
    toLex (1, Sum.inlₗ (toLex (base, index)))
| .flagSymbol id index =>
    toLex (2, Sum.inrₗ (toLex (id, index)))

private theorem orderKey_injective :
    Function.Injective orderKey := by
  intro left right hEq
  cases left <;> cases right <;>
    simp_all [orderKey]

instance : LinearOrder ProgramNames :=
  LinearOrder.lift' orderKey orderKey_injective

end ProgramNames

end Concrete

end Whiel

------------------------------------------------------------
-- Whiel-Name Order
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace WhielNames

/- Structural order key: copy, then program name. -/
private def orderKey : WhielNames → Nat ×ₗ ProgramNames
| .ordinary name => toLex (0, name)
| .prophecy name => toLex (1, name)

private theorem orderKey_injective :
    Function.Injective orderKey := by
  intro left right hEq
  cases left <;> cases right <;>
    simp_all [orderKey]

instance : LinearOrder WhielNames :=
  LinearOrder.lift' orderKey orderKey_injective

end WhielNames

end Concrete

end Whiel
