-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  PostgreSQL's foreign-key cascade, as the trigger queue runs it,
  against the declarative delete closure, each followed by the
  RESTRICT check.

  Inputs `SeedDel(k)` (unary: the keys the statement deletes),
  `RefBy(r, k)` (row r references key k through an ON DELETE
  CASCADE foreign key; rows are named by their own keys, so
  cascades chain) and `RestrictRef(r, k)` (row r references key k
  through a RESTRICT or NO ACTION foreign key), both binary.
  The delete closure is
    `Del(k) :- SeedDel(k)`
    `Del(r) :- RefBy(r, k), Del(k)`
  and the RESTRICT check reports the rows that reference a
  deleted key and still exist.

  Side 1, PostgreSQL (src/backend/utils/adt/ri_triggers.c, read
  2026-09-15): `RI_FKey_cascade_del` runs `DELETE FROM ONLY
  fktable WHERE $1 = fkatt1` for each deleted row, queued as an
  AFTER trigger and re-fired by the rows it deletes, a worklist
  of newly deleted rows; `ri_restrict` (RI_FKey_restrict_del,
  RI_FKey_noaction_del) runs `SELECT 1 FROM ONLY fktable x WHERE
  $1 = fkatt1 FOR KEY SHARE OF x` and raises a violation only if
  a referencing row still exists, so a row cascaded away in the
  same statement is not a violation.  Here side 1 keeps the check of legacy
  Example2024 instead, `Viol := π[0] (σ[#1 = #2] (RestrictRef ×
  Del))`, which reports every row referencing a deleted key,
  including the rows the same statement cascaded away.

  Side 2: the delete closure compiled by the naive compiler
  (`DelC_aux` is its snapshot), followed by the same check on
  `DelC`, `ViolC := π[0] (σ[#1 = #2] (RestrictRef × DelC)) ∖ DelC`.

  The two programs write disjoint relations and are merged side
  by side.  Precondition `true`.
  Postcondition `Del = DelC ∧ Viol = ViolC`.

  Expected verdict: invalid.  Witness: keys b and c are deleted,
  row a references b under CASCADE and c under RESTRICT.  Both
  sides delete a; the legacy check reports a as a violation, the
  surviving-reference check does not, since a no longer exists
  when the check runs.  The kernel counterexample is in
  Certificate/Invalid.lean.

  Why a database audience cares: this is the provenance
  correction of Example2024 as a case: modelling NO ACTION and
  RESTRICT as 'any reference to a deleted key' over-approximates
  PostgreSQL, which checks the referencing rows that remain.

  Sources: as Example5041.
-/

namespace Whiel
namespace Benchmark
namespace Example5042

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {SeedDel, Del, Front, New, Viol, DelC, DelC_aux, ViolC} (arity: 1),
    {RefBy, RestrictRef} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    true
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Del := SeedDel;
      Front := SeedDel;
      WHILE (Front ≠ ∅) DO
        New := ((π[0] (σ[#1 = #2] (RefBy × Front))) ∖ Del);
        Del := (Del ∪ New);
        Front := New
      END;
      Viol := (π[0] (σ[#1 = #2] (RestrictRef × Del)));
      DelC_aux := ∅[1];
      DelC := (SeedDel ∪ π[0] (σ[#1 = #2] ((RefBy × DelC_aux))));
      WHILE (¬((DelC = DelC_aux))) DO
        DelC_aux := DelC;
        DelC := (DelC ∪ (SeedDel ∪ π[0] (σ[#1 = #2] ((RefBy × DelC_aux)))))
      END;
      ViolC := ((π[0] (σ[#1 = #2] (RestrictRef × DelC))) ∖ DelC)
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((Del = DelC) ∧ (Viol = ViolC))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5042
end Benchmark
end Whiel
