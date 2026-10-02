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
  Postcondition `View ⊆ Filtered`.

  Expected verdict: valid.  Applying the exclusion at every step
  only removes pairs, so the per-step closure lies inside the
  unrestricted closure, and it never contains a banned pair; hence
  it lies inside the unrestricted closure minus the banned pairs.

  Expected obstruction: none (anchored).  Both loops advance one
  parent step per round, `View ⊆ ViewC` holds round by round
  together with `View ∩ Banned = ∅`, and the exclusion is applied
  after the compiled loop has finished, so a quantifier-free
  invariant certifies the containment.

  Why a database audience cares: the placement of a negation in
  a recursive definition changes its meaning; a rewriting that
  moves the exclusion outside the recursion (filter the closure
  view once) is only sound in one direction.  Example5040 states
  the equality and is refuted.

  Sources: authzed.com/docs/spicedb/concepts/schema (union,
  arrow, exclusion), read 2026-09-15; openfga/openfga main
  internal/graph/check.go `checkSetOperation` (exclusion = base
  and not subtract, per object), `checkTTU` (the arrow), read
  2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5039

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
    (View ⊆ Filtered)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5039
end Benchmark
end Whiel
