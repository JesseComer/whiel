-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Warshall's intermediate-vertex sweep, the boolean core of
  Floyd-Warshall, against PostgreSQL's recursive-union rounds.

  Inputs `Edge(x, y)` and the vertex order `Lt(x, y)`, both
  binary; the precondition states that `Lt` is a strict total
  order on the nodes of `Edge`.  The Datalog program both sides
  compute is the transitive closure
    `T(x, y) :- Edge(x, y)`
    `T(x, y) :- T(x, z), Edge(z, y)`

  Side 1, Floyd-Warshall (scipy/sparse/csgraph/_shortest_path.pyx,
  `floyd_warshall` and the Cython core `_floyd_warshall`, read
  2026-09-15: `for k in range(N): for i in range(N): if
  dist_matrix[i, k] == INFINITY: continue; for j in range(N):
  d_ijk = dist_matrix[i, k] + dist_matrix[k, j]; if d_ijk <
  dist_matrix[i, j]: dist_matrix[i, j] = d_ijk`, with the
  comment "In each loop, this finds the shortest path from point
  i to point j using intermediate nodes 0 ... k"; networkx/
  algorithms/shortest_paths/dense.py,
  `floyd_warshall_predecessor_and_distance`, read 2026-09-15:
  `for w in G: for u in G: for v in G: d = dist_u[w] +
  dist_w[v]; if dist_u[v] > d: ...`, and `floyd_warshall_numpy`,
  which applies the same sweep to the whole matrix at once, `A =
  np.minimum(A, A[i, :] + A[:, i])`).  Weights are not modelled:
  the boolean core keeps, for each intermediate vertex k taken
  in order, the pairs (i, j) with (i, k) and (k, j) present,
  which is the unit-weight reachability special case (a finite
  distance exists iff a path does; SciPy's `unweighted=True`
  sets every edge to 1).  The zero diagonal is not modelled
  either: the relation is reachability by one or more edges, so
  (i, i) appears exactly for the vertices on a cycle.  Within
  one sweep the in-place updates do not feed back, since an
  entry (i, k) or (k, j) cannot change during sweep k, so a
  sweep is one set-at-a-time step, as in the NumPy form.
  Encoding: `TW` starts as `Edge`; `Cur` is the `Lt`-least
  vertex of `Rest`, the vertices not yet swept; `InK` holds the
  pairs into `Cur`, `OutK` the pairs out of it, and the sweep
  adds `InK ∘ OutK`.  The claim holds for every order, that is
  for every strict total order `Lt`.

  Side 2, PostgreSQL (src/backend/executor/nodeRecursiveunion.c,
  `ExecRecursiveUnion`, read 2026-09-15; the loop of legacy
  Example2037 seeded with `Edge`): working table, already-seen
  check, intermediate table, stop when it is empty.

  Independent programs, merged side by side.  Precondition:
  `Lt` strict total order on the nodes; postcondition `TW =
  Res`.

  Expected verdict: valid.  After the sweeps of the first k
  vertices `TW` holds exactly the pairs joined by a path whose
  intermediate vertices are among them (Warshall's invariant),
  so after all sweeps it holds the pairs joined by any path,
  which is what the rounds compute.

  Expected obstruction: rate mismatch.  After k sweeps `TW`
  holds the paths whose intermediate vertices lie among the
  first k vertices of the order, unrelated to path length; after
  n rounds `Res` holds the paths of at most n+1 edges.  No
  first-order invariant over the current states relates them (a
  leveled-framework target).  Moreover the sweep composes two
  pairs of `TW`, so the containment `TW ⊆ Res∞` needs the
  transitivity of the executor's result, which follows from its
  leastness only and not from the fixpoint facts its exit
  provides (as for the squaring side of Example5007); the
  reverse containment
  `Res ⊆ TW∞` needs only that `TW∞` is closed under composition
  through every vertex, which the sweep's exit gives.  A harder
  target than Example5030.

  Why a database audience cares: all-pairs reachability is
  computed by dense matrix sweeps in scientific libraries and
  by recursive queries in databases, and the sweep is the
  textbook closure algorithm that optimisers and graph
  extensions use for small dense relations; the equality of the
  two is what lets a system choose either.  Example5035 is the
  invalid twin with a bound on the number of sweeps.

  Sources: scipy/scipy main (commit 884ac0b6fc53, 2026-09-15):
  scipy/sparse/csgraph/_shortest_path.pyx `floyd_warshall`,
  `_floyd_warshall`; read 2026-09-15.  networkx/networkx main
  (commit 4e74880b0da0, 2026-09-12): networkx/algorithms/
  shortest_paths/dense.py `floyd_warshall`,
  `floyd_warshall_predecessor_and_distance`,
  `floyd_warshall_numpy`; read 2026-09-15.  postgres/postgres
  master (commit 6e58d6356fcb, 2026-09-15): src/backend/
  executor/nodeRecursiveunion.c `ExecRecursiveUnion`; read
  2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5034

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Rest, Cur} (arity: 1),
    {Edge, Lt, TW, InK, OutK, Res, WorkT, Inter} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((((σ[#0 = #1] Lt) = ∅) ∧
        ((π[0, 3] (σ[#1 = #2] (Lt × Lt))) ⊆ Lt)) ∧
      ((Lt ⊆ ((π[0] Edge ∪ π[1] Edge) × (π[0] Edge ∪ π[1] Edge))) ∧
        ((σ[¬(#0 = #1)] ((π[0] Edge ∪ π[1] Edge) × (π[0] Edge ∪ π[1] Edge))) ⊆ (Lt ∪ π[1, 0] Lt))))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TW := Edge;
      Rest := (π[0] Edge ∪ π[1] Edge);
      WHILE (Rest ≠ ∅) DO
        Cur := (Rest ∖ (π[1] (σ[#0 = #2] (Lt × Rest))));
        InK := (π[0, 1] (σ[#1 = #2] (TW × Cur)));
        OutK := (π[1, 2] (σ[#0 = #1] (Cur × TW)));
        TW := (TW ∪ (π[0, 3] (σ[#1 = #2] (InK × OutK))));
        Rest := (Rest ∖ Cur)
      END;
      Res := Edge;
      WorkT := Edge;
      WHILE (WorkT ≠ ∅) DO
        Inter := ((π[0, 3] (σ[#1 = #2] (WorkT × Edge))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (TW = Res)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5034
end Benchmark
end Whiel
