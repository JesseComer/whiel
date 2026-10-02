-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Where the exclusion of a permission is applied: at every
  object, as SpiceDB and OpenFGA do, or once to the finished
  closure.

  Inputs `Reader(u, d)`, `Banned(u, d)` and `ParentRel(d, p)`
  (document d has parent p), all binary.  The permission is
  SpiceDB's `permission view = (reader + parent->view) - banned`
  (OpenFGA: `define view: (reader or view from parent) but not
  banned`): u views d if u reads d or views d's parent, and is
  not banned on d.

  Side 1 (legacy Example2036; authzed.com/docs/spicedb/concepts/
  schema and openfga/openfga internal/graph/check.go
  `checkSetOperation`, `checkTTU`, read 2026-09-15): the closure
  computed naively with the exclusion applied at every step, so
  a user banned on a document does not carry the permission down
  to its children:
    `View(u, d) :- Reader(u, d), not Banned(u, d)`
    `View(u, d) :- ParentRel(d, p), View(u, p), not Banned(u, d)`
  This is what both engines compute: the arrow reads the parent's
  permission, which already excludes the banned pairs.

  Side 2: the unrestricted closure
    `ViewC(u, d) :- Reader(u, d)`
    `ViewC(u, d) :- ParentRel(d, p), ViewC(u, p)`
  compiled by the naive compiler (`ViewC_aux` is its snapshot),
  followed by `Filtered := ViewC ∖ Banned`, the exclusion applied
  once at the end.

  The two programs write disjoint relations and are merged side
  by side.  Precondition `true`.
  Postcondition `View = Filtered`.

  Expected verdict: invalid.  Witness: u reads the parent p, is
  banned on p, and d is a child of p.  At every step: u never
  views p, so u does not view d.  Filtered once: the unrestricted
  closure gives u view on p and on d, and the final exclusion
  removes only (u, p), leaving (u, d).  The kernel counterexample
  is in Certificate/Invalid.lean.

  Why a database audience cares: this is the rewriting that is
  wrong, pushing a negation out of a recursive view; the
  counterexample is the ordinary case of an intermediate object
  on which the user is banned.

  Sources: as Example5039.
-/

namespace Whiel
namespace Benchmark
namespace Example5040

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Reader, Banned, ParentRel, View, View_aux, ViewC, ViewC_aux, Filtered} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    true
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      View_aux := ∅[2];
      View := (Reader ∖ Banned);
      WHILE (View ≠ View_aux) DO
        View_aux := View;
        View := ((Reader ∪ (π[2, 0] (σ[#1 = #3] (ParentRel × View_aux)))) ∖ Banned)
      END;
      ViewC_aux := ∅[2];
      ViewC := (Reader ∪ π[2,0] (σ[#1 = #3] ((ParentRel × ViewC_aux))));
      WHILE (¬((ViewC = ViewC_aux))) DO
        ViewC_aux := ViewC;
        ViewC := (ViewC ∪ (Reader ∪ π[2,0] (σ[#1 = #3] ((ParentRel × ViewC_aux)))))
      END;
      Filtered := (ViewC ∖ Banned)
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (View = Filtered)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5040
end Benchmark
end Whiel
