-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  NetworkX's transitive closure of a directed acyclic graph by
  a reverse topological sweep against PostgreSQL's
  recursive-union rounds.

  Inputs `Edge(x, y)` and `Lt(x, y)`, both binary.  The
  precondition states that `Lt` is a strict total order on the
  nodes of `Edge` and that the edges respect it, `Edge ⊆ Lt`:
  `Lt` is a topological order of the graph, which is therefore
  acyclic.  The Datalog program both sides compute is the
  transitive closure
    `T(x, y) :- Edge(x, y)`
    `T(x, y) :- T(x, z), Edge(z, y)`

  Side 1, NetworkX (networkx/algorithms/dag.py,
  `transitive_closure_dag(G, topo_order)`, read 2026-09-15):
  `TC = G.copy()`, then `for v in reversed(topo_order):
  TC.add_edges_from((v, u) for u in nx.descendants_at_distance(TC,
  v, 2))`, with the comment "traverse vertices following a
  reverse topological order, connecting each vertex to its
  descendants at distance 2 as we go".  `descendants_at_distance`
  (networkx/algorithms/traversal/breadth_first_search.py) returns
  the second layer of `bfs_layers` of the current `TC` from `v`:
  the nodes reached by two `TC` edges that are neither `v` nor
  direct successors of `v`; as a set, adding them to `v`'s row
  is `TC(v, ·) := TC(v, ·) ∪ TC(v, ·) ∘ TC` (`v` itself cannot
  be reached, the graph being acyclic, and direct successors are
  already in the row).  The successors of `v` come later in the
  order and have been processed, so their rows are complete and
  one step completes `v`'s row.  Encoding: `Cur` is the
  `Lt`-greatest node of `Rest`, the nodes not yet processed
  (the reverse of the topological order); `Row` is the rows of
  `Cur`; `TC := TC ∪ Row ∘ TC`.  A topological order is any
  strict total order containing the edges, so the claim holds
  for every such order.

  Side 2, PostgreSQL (src/backend/executor/nodeRecursiveunion.c,
  `ExecRecursiveUnion`, read 2026-09-15; the loop of legacy
  Example2037 seeded with `Edge`).

  Independent programs, merged side by side.  Precondition:
  `Lt` strict total order on the nodes and `Edge ⊆ Lt`;
  postcondition `TC = Res`.

  Expected verdict: valid.  When `v` is processed every node
  reachable from `v` is reachable through a successor `w` of
  `v` whose row is complete, so `Row ∘ TC` adds exactly the
  remaining descendants of `v`.

  Expected obstruction: rate mismatch.  One node absorbs the whole
  closures of its successors per step, while the rounds add one
  edge per round for every source, so no first-order invariant
  over the current states relates the two frontiers (a
  leveled-framework target); and, as in Example5034, the step
  composes two pairs of `TC`, so `TC ⊆ Res∞` needs the
  transitivity of the executor's result, which only its leastness
  gives.  The acyclicity that the algorithm needs is first-order
  here only because the order is data.

  Why a database audience cares: hierarchies (type lattices,
  dependency graphs, bills of materials) are DAGs, where a
  topological sweep beats the generic closure and where a
  database would write WITH RECURSIVE; the sweep's correctness
  rests on the order being topological, a precondition the
  recursive query does not need, which is what the claim makes
  explicit.

  Sources: networkx/networkx main (commit 4e74880b0da0,
  2026-09-12): networkx/algorithms/dag.py
  `transitive_closure_dag`; networkx/algorithms/traversal/
  breadth_first_search.py `descendants_at_distance`,
  `bfs_layers`; read 2026-09-15.  postgres/postgres master
  (commit 6e58d6356fcb, 2026-09-15): src/backend/executor/
  nodeRecursiveunion.c `ExecRecursiveUnion`; read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5036

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Rest, Cur} (arity: 1),
    {Edge, Lt, TC, Row, Res, WorkT, Inter} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (((((σ[#0 = #1] Lt) = ∅) ∧
        ((π[0, 3] (σ[#1 = #2] (Lt × Lt))) ⊆ Lt)) ∧
      ((Lt ⊆ ((π[0] Edge ∪ π[1] Edge) × (π[0] Edge ∪ π[1] Edge))) ∧
        ((σ[¬(#0 = #1)] ((π[0] Edge ∪ π[1] Edge) × (π[0] Edge ∪ π[1] Edge))) ⊆ (Lt ∪ π[1, 0] Lt)))) ∧
      (Edge ⊆ Lt))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TC := Edge;
      Rest := (π[0] Edge ∪ π[1] Edge);
      WHILE (Rest ≠ ∅) DO
        Cur := (Rest ∖ (π[0] (σ[#1 = #2] (Lt × Rest))));
        Row := (π[1, 2] (σ[#0 = #1] (Cur × TC)));
        TC := (TC ∪ (π[0, 3] (σ[#1 = #2] (Row × TC))));
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
    (TC = Res)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5036
end Benchmark
end Whiel
