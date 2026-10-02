-- Author: Jesse Comer
import Databases.FinStruct.Basic
import Databases.UnnamedModel.Instance

/-
  This file translates function-expanded finite structures
  back to unnamed database instances.

  Key definitions include:
    * `FinStruct.toInstance`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Finite Structures as Unnamed Instances
------------------------------------------------------------

namespace FinStruct

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

/-
  Forget functions and carrier to recover the relational
  instance represented by a function-expanded structure.
-/
def toInstance
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C)) :
    Instance D Γ :=
  fun X => M.rels X

end FinStruct
