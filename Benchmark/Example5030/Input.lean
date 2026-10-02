-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  NetworkX's per-source transitive closure against
  PostgreSQL's recursive-union rounds.

  Inputs `Edge(x, y)` and the node order `Lt(x, y)`, both
  binary.  The precondition states that `Lt` is a strict total
  order on the nodes of `Edge`: irreflexive, transitive,
  contained in nodes × nodes, and total.  The Datalog program
  both sides compute is the transitive closure
    `T(x, y) :- Edge(x, y)`
    `T(x, y) :- T(x, z), Edge(z, y)`

  Side 1, NetworkX (networkx/algorithms/dag.py,
  `transitive_closure(G, reflexive=False)`, read 2026-09-15):
  `for v in G:` add `(v, e[1])` for every edge `e` yielded by
  `nx.edge_bfs(G, v)` (networkx/algorithms/traversal/edgebfs.py):
  a breadth-first search over the edges out of the visited
  nodes, starting at `v`, that enqueues each newly reached head
  once ("if child not in visited_nodes") and yields every edge
  out of a visited node once, including edges back into visited
  nodes, which is why the docstring says that "non-trivial
  cycles create self-loops".  (The handoff names
  `nx.descendants`; in the current source that node-level BFS
  serves only `reflexive=None` and `reflexive=True`.  The two
  differ only on the pair `(v, v)`, which `edge_bfs` reports for
  a cycle through `v` and `descendants` never does.)  Encoding:
  the outer loop takes the nodes in `Lt` order, `Cur` being the
  `Lt`-least node of `Rest`, the nodes not yet processed; the
  inner loop is the edge BFS from `Cur` set-at-a-time: `Vis` the
  visited nodes as pairs `(Cur, node)`, seeded with `(Cur,
  Cur)`; `Fr` the nodes visited in the last round; `Step` the
  heads of the edges out of `Fr`, all added to `Tca`; `New =
  Step ∖ Vis` is the next frontier.  The order in which the
  queue serves nodes affects neither the visited set nor the set
  of edges yielded, so the FIFO queue is rendered level by
  level.  `for v in G` visits every node once, and so does the
  cursor for every strict total order `Lt`: the claim holds for
  every order.  (`First(x)` and `Next(x, y)` as inputs would not
  do: that the walk along `Next` from `First` reaches every node
  is not first-order, and for a partial enumeration the two
  closures differ.)

  Side 2, PostgreSQL (src/backend/executor/nodeRecursiveunion.c,
  `ExecRecursiveUnion`, read 2026-09-15; the legacy Example2037
  loop, as in Example5001): for `WITH RECURSIVE tc AS (SELECT x,
  y FROM edge UNION SELECT tc.x, e.y FROM tc JOIN edge e ON tc.y
  = e.x)` the working table `WorkT` holds the last round's rows,
  the recursive term is evaluated against it, rows already in
  the result are dropped ("Ignore tuple if already seen"), the
  intermediate table `Inter` becomes the next working table and
  the loop stops when it is empty (header comment, steps
  2.1-2.6).

  The two programs write disjoint relations; the preprocessor
  merges them side by side and draws one flag for the nested
  loop.  Precondition: `Lt` is a strict total order on the
  nodes; postcondition `Tca = Res`.

  Expected verdict: valid.  Both relations are the set of pairs
  joined by a path of one or more edges.

  Expected obstruction: rate mismatch.  After n rounds the
  executor holds, for every source, the pairs joined by at most
  n+1 edges; the per-source side holds complete rows for the
  sources before the cursor and a partial breadth-first row for
  the cursor, so no first-order invariant over the current
  states relates the two frontiers (a leveled-framework target).
  With the final values as prophecy constants the containments
  `Tca ⊆ Res∞` and `Res ⊆ Tca∞` need only the single-edge
  closure facts each loop's exit provides, not the leastness of
  the other side's fixpoint, unlike Example5007.

  Why a database audience cares: graph libraries and SQL
  engines both offer transitive closure, and pipelines move
  between them (a NetworkX closure materialised into a table, a
  WITH RECURSIVE view replacing a Python loop); the per-source
  breadth-first search and the recursive union are the two
  standard evaluation orders, and their agreement is what
  licenses the swap.  Example5031 is the invalid twin with a
  depth cutoff on the per-source side.

  Sources: networkx/networkx main (commit 4e74880b0da0,
  2026-09-12): networkx/algorithms/dag.py `transitive_closure`,
  `descendants`; networkx/algorithms/traversal/edgebfs.py
  `edge_bfs`; read 2026-09-15.  postgres/postgres master (commit
  6e58d6356fcb, 2026-09-15): src/backend/executor/
  nodeRecursiveunion.c `ExecRecursiveUnion`; read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5030

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Rest, Cur} (arity: 1),
    {Edge, Lt, Vis, Fr, Step, New, Tca, Res, WorkT, Inter} (arity: 2)
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
      Tca := ∅[2];
      Rest := (π[0] Edge ∪ π[1] Edge);
      WHILE (Rest ≠ ∅) DO
        Cur := (Rest ∖ (π[1] (σ[#0 = #2] (Lt × Rest))));
        Vis := (π[0, 0] Cur);
        Fr := Vis;
        WHILE (Fr ≠ ∅) DO
          Step := (π[0, 3] (σ[#1 = #2] (Fr × Edge)));
          Tca := (Tca ∪ Step);
          New := (Step ∖ Vis);
          Vis := (Vis ∪ New);
          Fr := New
        END;
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
    (Tca = Res)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5030
end Benchmark
end Whiel
