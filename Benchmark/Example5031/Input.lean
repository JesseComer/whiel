-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  The invalid twin of Example5030: a per-source search with a
  depth cutoff against PostgreSQL's recursive-union rounds.

  Inputs `Edge(x, y)` and the node order `Lt(x, y)` as in
  Example5030 (precondition: `Lt` is a strict total order on the
  nodes).  The Datalog program of side 2 is the closure
    `T(x, y) :- Edge(x, y)`
    `T(x, y) :- T(x, z), Edge(z, y)`

  Side 1, NetworkX (networkx/algorithms/shortest_paths/
  unweighted.py, `single_source_shortest_path_length(G, source,
  cutoff)` and its helper `_single_shortest_path_length`, read
  2026-09-15): `seen = set(firstlevel)`, level 0 yields the
  source itself, then `while nextlevel and cutoff > level:` the
  level advances and every neighbour `w` of the level's nodes
  that is not in `seen` is added to `seen` and yielded with the
  new level.  With `cutoff=2` the function returns the nodes at
  distance at most 2 from the source.  A closure built from it,
  `(v, w)` for every `v` in order and every `w` yielded at level
  1 or 2, is what the outer loop collects in `TcB`: `SeenA` is
  the seen set `{v}` (as pairs), `LvlA` the level-1 nodes,
  `SeenB` the seen set after level 1, `LvlB` the level-2 nodes.
  The bounded search is loop-free, so this side has one loop,
  the cursor over the order (as in Example5030, the `Lt`-least
  node of `Rest`).

  Side 2, PostgreSQL `ExecRecursiveUnion` rounds on the closure
  query (as in Example5030).

  Precondition: `Lt` strict total order on the nodes;
  postcondition `TcB = Res`.

  Expected verdict: invalid.  Witness: the path 0→1→2→3 with the
  order 0<1<2<3: the executor derives (0, 3) in its second
  recursive round, the search from 0 stops after level 2 and
  never reports 3
  (kernel-checked in Certificate/Invalid.lean).  The control
  0→1→2 with the same order is not a counterexample.  A second
  discrepancy, not needed for the witness: `seen` contains the
  source from the start, so a walk back to the source is never
  yielded, and on the 2-cycle 0↔1 the executor holds (0, 0) and
  (1, 1) while the cutoff side does not (third check instance);
  `transitive_closure(reflexive=False)` reports those pairs
  because `edge_bfs` yields edges into visited nodes.

  Why a database audience cares: a depth cutoff is the usual
  way to bound a recursive search (compare SQL Server's
  MAXRECURSION and MySQL's cte_max_recursion_depth), and a
  bounded per-source search silently truncates long paths while
  agreeing with the closure on every short instance; the rate
  mismatch with the executor's rounds is the same as in
  Example5030, so an invariant argument would have to see the
  cutoff.

  Sources: networkx/networkx main (commit 4e74880b0da0,
  2026-09-12): networkx/algorithms/shortest_paths/unweighted.py
  `single_source_shortest_path_length`,
  `_single_shortest_path_length`; read 2026-09-15.
  postgres/postgres master (commit 6e58d6356fcb, 2026-09-15):
  src/backend/executor/nodeRecursiveunion.c
  `ExecRecursiveUnion`; read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5031

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Rest, Cur} (arity: 1),
    {Edge, Lt, SeenA, LvlA, SeenB, LvlB, TcB, Res, WorkT, Inter} (arity: 2)
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
      TcB := ∅[2];
      Rest := (π[0] Edge ∪ π[1] Edge);
      WHILE (Rest ≠ ∅) DO
        Cur := (Rest ∖ (π[1] (σ[#0 = #2] (Lt × Rest))));
        SeenA := (π[0, 0] Cur);
        LvlA := ((π[0, 3] (σ[#1 = #2] (SeenA × Edge))) ∖ SeenA);
        SeenB := (SeenA ∪ LvlA);
        LvlB := ((π[0, 3] (σ[#1 = #2] (LvlA × Edge))) ∖ SeenB);
        TcB := ((TcB ∪ LvlA) ∪ LvlB);
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
    (TcB = Res)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5031
end Benchmark
end Whiel
