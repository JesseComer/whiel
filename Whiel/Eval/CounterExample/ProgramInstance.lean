-- Author: Jesse Comer
import Whiel.Concrete.WhielNames.Notation
import Whiel.Concrete.Data
import Whiel.Hoare.Concrete

/-
  Literal instances over a program-name input schema.

  A counterexample certificate must name its instance in
  source without a schema-specific notation, because the
  concrete `inst![...]` notation is defined only for the
  `IndexAlphaName` carrier. `ofKeyedRows` rebuilds one
  complete instance from relation rows keyed by the
  canonical `ProgramNames.encode` key, so a generated
  certificate carries the frozen instance as an ordinary
  list literal that the kernel reduces.

  Key definitions:
    * `Whiel.Concrete.ProgramInstance.ofKeyedRows`
-/

------------------------------------------------------------
-- Keyed Program Instances
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace ProgramInstance

/- Tuples of one relation, as lists of domain values. -/
abbrev Rows := List (List Data)

/- Relation rows keyed by canonical program-name keys. -/
abbrev KeyedRows := List (String × Rows)

/- Rows recorded for one canonical relation key. -/
def rowsOfKey (key : String) : KeyedRows → Rows
| [] => []
| (name, rows) :: rest =>
    if name == key then rows else rowsOfKey key rest

/- Rows of the right length, as one finite relation. -/
def relationOfRows (n : Nat) : Rows → FinRelation Data n
| [] => ∅
| cells :: rest =>
    match Tuple.ofList? n cells with
    | some tuple => insert tuple (relationOfRows n rest)
    | none => relationOfRows n rest

/-
  One complete instance over an input schema, read off
  canonical relation keys. A key that the schema does not
  name is ignored, and a row of the wrong length is dropped:
  the caller re-checks the rebuilt instance rather than
  trusting the literal.
-/
def ofKeyedRows
    (Gamma : UnnamedSchema ProgramNames)
    (rows : KeyedRows) : Instance Data Gamma :=
  fun X =>
    relationOfRows (Gamma.arity X)
      (rowsOfKey (ProgramNames.encode X.1) rows)

end ProgramInstance

end Concrete

end Whiel
