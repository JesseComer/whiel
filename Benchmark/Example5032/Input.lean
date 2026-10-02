-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Delta-driven incremental maintenance of a transitive closure
  under insertions against PostgreSQL's recomputation on the
  updated edge set.

  Inputs `EBase(x, y)`, the edges before the update, and
  `EDelta(x, y)`, the inserted edges (both binary).  The Datalog
  program is the closure of the current edges,
    `T(x, y) :- E(x, y)`
    `T(x, y) :- T(x, z), E(z, y)`
  with `E = EBase` for the old view and `E = EBase ∪ EDelta` for
  the new one.

  Phase 1 (compiled by the naive compiler; `TOld_aux` is its
  snapshot) computes the old view `TOld`, the closure of
  `EBase`, so that its exactness is by construction, as in
  Example5005:
    `TOld(x, y) :- EBase(x, y)`
    `TOld(x, y) :- TOld(x, z), EBase(z, y)`

  Phase 2, the delta-driven maintainer, hand-written.  The
  incremental engines evaluate a recursive view on a change of
  its inputs by propagating changes only.  Materialize
  (doc/user/content/sql/select/recursive-ctes.md, read
  2026-09-15): "For each iteration, Materialize performs work
  resulting only from the input changes for this iteration and
  feeds back the resulting output changes to the next
  iteration."  DBSP (Budiu, McSherry, Ryzhyk, Tannen, "DBSP:
  Automatic Incremental View Maintenance for Rich Query
  Languages", VLDB 2023, section 6, read 2026-09-15): the
  incremental circuit "preserves the stream of changes to
  recursive relations produced by the iterative fixed point
  computation, and adjusts this stream to account for the
  modified inputs"; its section 5.1 notes that the fixed-point
  circuit computes the changes of each iteration and stops when
  "the set of new facts becomes empty", which "effectively
  implements the semi-naive evaluation algorithm".  Feldera
  (crates/dbsp/src/operator/recursive.rs, `Circuit::recursive`,
  read 2026-09-15): "at each clock cycle, the parent circuit
  feeds an update Δi to the external input i of the nested
  circuit, and the nested circuit computes Δx = y - x, where y
  is a solution to the equation y = f(i+Δi, y)"; the SQL
  documentation (docs.feldera.com/docs/sql/recursion.mdx) states
  that recursive views "start out empty and are computed
  iteratively until they reach a stable state" and that
  deletions "are recomputed incrementally as well".  For an
  insert-only update under set semantics the total change is
  the new view minus the old one, and the set-level rendering
  of "work resulting only from the input changes" is the delta
  rule of semi-naive evaluation restarted from the old fixpoint:
  the seed `Delta` holds the consequences of the inserted edges
  given the old view, `EDelta ∪ TOld ∘ EDelta`, minus what the
  old view already holds; each round extends only the last delta
  by one edge of the new graph and discards what is already
  derived; the old view is never re-derived.  Not modelled:
  DBSP's Z-set weights and its re-differencing of the earlier
  iterations in nested time (a fact that moves to an earlier
  round appears there as a retraction and a re-insertion); the
  loop keeps only the set-level result of those operations.
  The rule orientation follows the recomputing engine, which
  appends an edge; DBSP's transitive-closure example prepends
  one, which changes nothing in the maintained relation.

  Phase 3, PostgreSQL rounds (src/backend/executor/
  nodeRecursiveunion.c, `ExecRecursiveUnion`, read 2026-09-15;
  the loop of legacy Example2037) recompute the closure of
  `EBase ∪ EDelta` from scratch: the working table `WorkT` holds
  the last round's rows, rows already in the result are dropped,
  the intermediate table becomes the next working table, and
  the loop stops when it is empty.

  Phase 2 reads phase 1's output, so the preprocessor draws
  flags: the closure of `EBase` runs first, and when it is
  complete the maintainer and the recomputation (which writes
  disjoint relations) are started together and run side by
  side.  Precondition `true`; postcondition `T = Res`.

  Expected verdict: valid.  The maintainer iterates the new
  closure operator from the old view, which is contained in the
  new closure, so it converges to the new closure, and so does
  the recomputation.

  Expected obstruction: dependent phases and rate mismatch. The
  maintainer starts only when the old view is complete; its
  round i then holds the old view plus the pairs joined by a
  path with an inserted edge followed by at most i-1 further
  edges, while the recomputation's round n holds the pairs
  joined by at most n+1 edges of the new graph, so no
  first-order invariant over the current states relates the two
  frontiers (a leveled-framework target).  With the final values
  as prophecy constants, `T ⊆ Res∞` follows from `Res∞ ⊇ EBase ∪
  EDelta` and `Res∞ ∘ (EBase ∪ EDelta) ⊆ Res∞`, and `Res ⊆ T∞`
  from the maintainer's exit facts `T∞ ⊇ EBase ∪ EDelta` and
  `T∞ ∘ (EBase ∪ EDelta) ⊆ T∞`; no leastness is needed.  It
  differs from Example5005, whose maintainer restarts a naive
  evaluation from the old view and re-derives every fact each
  round: this one propagates only the delta.

  Why a database audience cares: incremental view maintenance
  is what streaming and incremental engines sell, and the delta
  rule (seed with the consequences of the change, propagate the
  frontier, never touch the old view) is the algorithm behind
  it; the claim that it reproduces the recomputed view is the
  core correctness obligation, and the classic bug is a missing
  seed term such as `TOld ∘ EDelta`.

  Sources: MaterializeInc/materialize main (commit 4e1db20efcc4,
  2026-09-15): doc/user/content/sql/select/recursive-ctes.md,
  read 2026-09-15.  Budiu, McSherry, Ryzhyk, Tannen, DBSP, VLDB
  2023 (arXiv 2203.16684): sections 5.1, 6, 6.1, 6.2, read
  2026-09-15.  feldera/feldera main (commit 16c3f5324fa0,
  2026-09-15): crates/dbsp/src/operator/recursive.rs
  (`Circuit::recursive` documentation),
  docs.feldera.com/docs/sql/recursion.mdx, read 2026-09-15.
  postgres/postgres master (commit 6e58d6356fcb, 2026-09-15):
  src/backend/executor/nodeRecursiveunion.c
  `ExecRecursiveUnion`, read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5032

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {EBase, EDelta, TOld, TOld_aux, Delta, T, Res, WorkT, Inter} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    true
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TOld_aux := ∅[2];
      TOld := (EBase ∪ π[0,3] (σ[#1 = #2] ((TOld_aux × EBase))));
      WHILE (¬((TOld = TOld_aux))) DO
        TOld_aux := TOld;
        TOld := (TOld ∪ (EBase ∪ π[0,3] (σ[#1 = #2] ((TOld_aux × EBase)))))
      END;
      Delta := ((EDelta ∪ (π[0, 3] (σ[#1 = #2] (TOld × EDelta)))) ∖ TOld);
      T := (TOld ∪ Delta);
      WHILE (Delta ≠ ∅) DO
        Delta := ((π[0, 3] (σ[#1 = #2] (Delta × (EBase ∪ EDelta)))) ∖ T);
        T := (T ∪ Delta)
      END;
      Res := (EBase ∪ EDelta);
      WorkT := (EBase ∪ EDelta);
      WHILE (WorkT ≠ ∅) DO
        Inter := ((π[0, 3] (σ[#1 = #2] (WorkT × (EBase ∪ EDelta)))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (T = Res)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5032
end Benchmark
end Whiel
