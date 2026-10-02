-- Author: Jesse Comer
import Databases.FinStruct.PrettyPrint

/-
  Typed notation for finite-structure examples.

  Key declarations include:
    * `finstruct![...]`
    * `finstruct?[...]`
-/

------------------------------------------------------------
-- Finite-Structure Constructors
------------------------------------------------------------

namespace FinStruct

namespace Notation

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Λ : Signature A F}

/- Build a finite structure from checked raw data. -/
def checked
    (carrier : Finset D)
    (rels :
      (X : Signature.Rel Λ) →
        FinRelation D (Λ.arity X))
    (funcs :
      (f : Signature.Fun Λ) →
        Tuple D (Λ.funArity f) → D)
    (hNonempty : carrier.Nonempty)
    (hRels : FinStruct.RelClosed carrier rels)
    (hFuncs : FinStruct.FuncClosed carrier funcs) :
    FinStruct D Λ where
  carrier := carrier
  carrier_nonempty := hNonempty
  rels := rels
  rels_closed := by
    intro X t ht
    exact hRels X t ht
  funcs := funcs
  funcs_closed := by
    intro f args hArgs
    exact hFuncs f args hArgs

end Notation

end FinStruct

------------------------------------------------------------
-- Finite-Structure Literals
------------------------------------------------------------

syntax
  "finstruct?[" "carrier " term "; "
    "rels " term "; " "funcs " term "]" :
  term

macro_rules
| `(finstruct?[
      carrier $C:term; rels $R:term; funcs $F:term]) =>
    `(FinStruct.mk? $C $R $F)

syntax
  "finstruct![" "carrier " term "; "
    "rels " term "; " "funcs " term "]" :
  term

macro_rules
| `(finstruct![
      carrier $C:term; rels $R:term; funcs $F:term]) =>
    `(FinStruct.Notation.checked
      $C $R $F (by decide) (by decide) (by decide))
