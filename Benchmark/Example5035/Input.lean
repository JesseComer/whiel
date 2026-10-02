-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  The invalid twin of Example5034: Warshall's sweep stopped
  after the first two vertices of the order, against PostgreSQL's
  recursive-union rounds.

  Inputs `Edge(x, y)` and the vertex order `Lt(x, y)` as in
  Example5034 (precondition: `Lt` is a strict total order on the
  nodes).  The Datalog program of side 2 is the closure
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
  Here the outer loop `for k in range(N)` is cut after two
  iterations: `KA` is the `Lt`-least vertex, `KB` the least of
  the rest; `TWa` is `Edge` plus the pairs through `KA`, `TWb`
  is `TWa` plus the pairs through `KB`.  The bounded sweep is
  loop-free and each relation is assigned once, so the
  preprocessor carries it into the precondition and the
  verified loop is the executor's.

  Side 2, PostgreSQL `ExecRecursiveUnion` rounds on the closure
  query (as in Example5034).

  Precondition: `Lt` strict total order on the nodes;
  postcondition `TWb = Res`.

  Expected verdict: invalid.  Witness: the path 0→1→2→3 with the
  order 0<1<2<3: the sweep of 0 adds nothing (no pair into 0),
  the sweep of 1 adds (0, 2), and (0, 3) and (1, 3), which need
  the intermediate vertex 2, are never added, while the executor
  derives them (kernel-checked in Certificate/Invalid.lean).
  The control 1→0→2 with the order 0<1<2 is not a
  counterexample: its only path through an intermediate vertex
  goes through 0.  The 3-cycle 0→1→2→0 with the order 0<1<2 is a
  second witness (nine pairs against six).

  Why a database audience cares: a sweep cut short is not a
  closure truncated by depth: unlike a bounded round count it
  misses paths of every length, namely all those whose
  intermediate vertices lie outside the swept prefix, so a
  partitioned or budget-limited sweep (one worker's prefix of
  the vertex order) silently returns a relation that agrees
  with the closure on some inputs and not on others.

  Sources: as Example5034 (scipy/scipy main, commit
  884ac0b6fc53, scipy/sparse/csgraph/_shortest_path.pyx;
  networkx/networkx main, commit 4e74880b0da0,
  networkx/algorithms/shortest_paths/dense.py; postgres/postgres
  master, commit 6e58d6356fcb, src/backend/executor/
  nodeRecursiveunion.c; all read 2026-09-15).
-/

namespace Whiel
namespace Benchmark
namespace Example5035

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {KA, RestB, KB} (arity: 1),
    {Edge, Lt, InA, OutA, TWa, InB, OutB, TWb, Res, WorkT, Inter} (arity: 2)
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
      KA := ((π[0] Edge ∪ π[1] Edge) ∖ (π[1] Lt));
      RestB := ((π[0] Edge ∪ π[1] Edge) ∖ KA);
      KB := (RestB ∖ (π[1] (σ[#0 = #2] (Lt × RestB))));
      InA := (π[0, 1] (σ[#1 = #2] (Edge × KA)));
      OutA := (π[1, 2] (σ[#0 = #1] (KA × Edge)));
      TWa := (Edge ∪ (π[0, 3] (σ[#1 = #2] (InA × OutA))));
      InB := (π[0, 1] (σ[#1 = #2] (TWa × KB)));
      OutB := (π[1, 2] (σ[#0 = #1] (KB × TWa)));
      TWb := (TWa ∪ (π[0, 3] (σ[#1 = #2] (InB × OutB))));
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
    (TWb = Res)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5035
end Benchmark
end Whiel
