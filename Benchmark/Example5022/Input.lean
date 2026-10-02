-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Recursion limits of SQL engines: a recursive CTE run under
  MySQL's cte_max_recursion_depth or SQL Server's
  MAXRECURSION against the Datalog closure it is meant to
  compute.  Claim: when the engine does not abort, its
  result is the closure.

  Inputs `Base(x, y)`, the rows of the anchor member, and
  `E(y, z)`, the table the recursive member joins with.  The
  CTE is
    WITH RECURSIVE r(x, y) AS (SELECT x, y FROM Base
      UNION DISTINCT SELECT r.x, E.z FROM r JOIN E ON r.y = E.y)
    SELECT * FROM r
  that is the query
    `Cl(x, y) :- Base(x, y)`
    `Cl(x, z) :- Cl(x, y), E(y, z)`.

  Side 1, the engine under the recursion limit k = 4 (MySQL
  SET cte_max_recursion_depth = 4; SQL Server OPTION
  (MAXRECURSION 4)).  MySQL (Reference Manual 8.4, "WITH
  (Common Table Expressions)", sections "Recursive Common
  Table Expressions" and "Limiting Common Table Expression
  Recursion", read 2026-09-15): "Each iteration of the
  recursive part operates only on the rows produced by the
  previous iteration"; with UNION DISTINCT "duplicate rows
  are eliminated", which "is useful for queries that perform
  transitive closures, to avoid infinite loops"; "Recursion
  ends when this part produces no new rows"; and "The server
  terminates execution of any CTE that recurses more levels
  than the value of this variable" (default 1000), raising
  error 3636 ER_CTE_MAX_RECURSION_DEPTH, "Recursive query
  aborted after %u iterations. Try increasing
  @@cte_max_recursion_depth to a larger value."  Encoded
  loop-free with one relation per iteration (names may not
  carry digits, and each relation must be assigned once for
  the preprocessor to carry the computation into the
  precondition): `ResA = Base` is the anchor's result;
  `NewB` the new rows of iteration 1 (the join of the rows
  produced by the previous iteration with `E`, minus the
  rows already in the result), `ResB` the result after it,
  and so on to `NewE`, `ResE` after iteration 4.  The engine
  returns `ResE` exactly when iteration 4 produced no new
  rows, `NewE = ∅`; otherwise iteration 5 would be needed and
  the statement is aborted.  SQL Server ("WITH
  common_table_expression (Transact-SQL)", read 2026-09-15:
  "UNION ALL is the only set operator allowed between the
  last anchor member and first recursive member";
  MAXRECURSION takes "a value between 0 and 32767", "The
  server-wide default is 100"; error 530 "The statement
  terminated. The maximum recursion %d has been exhausted
  before statement completion.") keeps duplicates and stops
  only when an iteration produces no row at all, which
  implies `NewE = ∅`; so whenever SQL Server completes, the
  claim below applies to its result as well (on cyclic data
  it never completes without a cycle guard).  Whether an
  engine checks the bound at iteration k or k + 1 shifts k
  by one; the claim holds for every k, and k = 4 keeps the
  case small.

  Side 2, the closure (compiled by the naive compiler from
  the two rules above), snapshot `Cl_aux`.

  Precondition `true`; postcondition
    `(NewE ≠ ∅) ∨ (Cl = ResE)`,
  "the recursion terminated within the limit implies its
  result is the closure".

  Expected verdict: valid.  If `NewE = ∅` then `ResD` is
  closed under an `E` step (the successors of each `New` set
  lie in the next `Res`, and those of `NewD` in `ResD`) and
  contains `Base`, so it contains the least fixpoint `Cl`;
  and every `Res` row is a path, so `ResE ⊆ Cl`.  Expected
  obstruction: a disjunctive invariant.  On instances that
  exceed the bound the closure is not contained in `ResE`,
  so no conjunction of inclusions between `Cl` and the
  engine's relations is inductive; the inductive invariant
  is `NewE ≠ ∅ ∨ Cl ⊆ ResE` together with the unrolled
  inclusions `ResE ⊆ Cl`-side, a Boolean combination.  This
  is not Example5012/5013 (a bounded naive unrolling
  contained in, or equal to, the closure, unconditionally):
  the engine's level is semi-naive and the claim is
  conditional on termination.

  Why it matters: application code takes a recursive CTE
  that returns to have returned the whole closure; the limit
  turns silent truncation into an error, and this case is
  the statement that the error is the only way to get less
  than the closure.

  Sources: MySQL 8.4 Reference Manual, "WITH (Common Table
  Expressions)", https://dev.mysql.com/doc/refman/8.4/en/with.html,
  read 2026-09-15; MySQL server source
  share/messages_to_clients.txt, branch 8.4 at commit
  99960bf74fa919347e4f4e3ca47672f333d6e91f,
  https://github.com/mysql/mysql-server/blob/8.4/share/messages_to_clients.txt
  (ER_CTE_MAX_RECURSION_DEPTH, number 3636 by the file's
  start-error-number 3500 sequence), read 2026-09-15.
  Microsoft SQL Server, "WITH common_table_expression
  (Transact-SQL)",
  https://learn.microsoft.com/en-us/sql/t-sql/queries/with-common-table-expression-transact-sql
  (guidelines for defining and using recursive CTEs; "Use
  MAXRECURSION to cancel a statement"); "Hints (Transact-SQL)
  - Query",
  https://learn.microsoft.com/en-us/sql/t-sql/queries/hints-transact-sql-query
  (MAXRECURSION <integer_value>); "Database Engine events
  and errors (0 to 999)",
  https://learn.microsoft.com/en-us/sql/relational-databases/errors-events/database-engine-events-and-errors-0-to-999
  (error 530); all read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5022

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Base, E, ResA, NewB, ResB, NewC, ResC, NewD, ResD, NewE, ResE, Cl, Cl_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      ResA := Base;
      NewB := (π[0, 3] (σ[#1 = #2] (ResA × E)) ∖ ResA);
      ResB := (ResA ∪ NewB);
      NewC := (π[0, 3] (σ[#1 = #2] (NewB × E)) ∖ ResB);
      ResC := (ResB ∪ NewC);
      NewD := (π[0, 3] (σ[#1 = #2] (NewC × E)) ∖ ResC);
      ResD := (ResC ∪ NewD);
      NewE := (π[0, 3] (σ[#1 = #2] (NewD × E)) ∖ ResD);
      ResE := (ResD ∪ NewE);
      Cl_aux := ∅[2];
      Cl := (Base ∪ π[0,3] (σ[#1 = #2] ((Cl_aux × E))));
      WHILE (¬((Cl = Cl_aux))) DO
      Cl_aux := Cl;
      Cl := (Cl ∪ (Base ∪ π[0,3] (σ[#1 = #2] ((Cl_aux × E)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((NewE ≠ ∅) ∨ (Cl = ResE))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5022
end Benchmark
end Whiel
