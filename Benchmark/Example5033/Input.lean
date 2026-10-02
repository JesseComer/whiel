-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Soufflé's magic-set (demand-driven) evaluation of a
  right-linear path query with a bound source against
  PostgreSQL's bulk evaluation of the original query restricted
  to the demanded sources.

  Inputs `Edge(x, y)` (binary) and the demand seed `Root(x)`
  (unary), pinned by the precondition to the single source
  `"root"` as Example2004 does.  The original program is
    `Path(x, y) :- Edge(x, y)`
    `Path(x, z) :- Edge(x, y), Path(y, z)`
  asked with the first argument bound, `Path("root", y)`.

  Side 1, Soufflé (src/ast/transform/MagicSet.cpp:
  `MagicSetCoreTransformer::transform`, `createMagicClause`,
  `createMagicAtom`, `getMagicName`; and the documentation page
  souffle-lang.github.io/magicset, both read 2026-09-15).
  Constraint normalisation replaces the constant by a
  constrained variable; adornment gives `Path` the pattern `bf`
  (first argument bound, the SIPS takes the left-most atom with
  a bound argument); the transformation adds, for each IDB body
  atom `Ai` of an adorned clause `A_a :- A1_a1, ..., An_an`, the
  magic clause `magic(Ai_ai) :- magic(A_a), A1_a1, ...,
  A(i-1)_a(i-1)` and replaces the clause by `A_a :- magic(A_a),
  A1_a1, ..., An_an`; the magic atom carries the bound arguments
  only (`createMagicAtom` copies the arguments whose adornment
  is 'b') and is named by prepending "@magic" (`getMagicName`).
  For this program, with `@magic_Path_bf` written `MPath`, the
  output is the program of Example2003/2004,
    `MPath(x) :- Root(x)`
    `MPath(y) :- MPath(x), Edge(x, y)`
    `PathBF(x, y) :- MPath(x), Edge(x, y)`
    `PathBF(x, z) :- MPath(x), Edge(x, y), PathBF(y, z)`
  compiled by the naive compiler; `MPath_aux` and `PathBF_aux`
  are its snapshots.

  Side 2, PostgreSQL (src/backend/executor/nodeRecursiveunion.c,
  `ExecRecursiveUnion`, read 2026-09-15; the loop of legacy
  Example2037): the recursive union for the original query,
  `WITH RECURSIVE path AS (SELECT x, y FROM edge UNION SELECT
  e.x, p.z FROM edge e JOIN path p ON e.y = p.x)`, whose
  recursive term prepends an edge to the last round's rows
  (`Edge × WorkT`), computes every source's rows; rows already
  seen are dropped and the loop stops when the intermediate
  table is empty.  The restriction to the demanded sources is
  the join of the answers with the demand set, stated in the
  postcondition.

  The two programs write disjoint relations and are merged side
  by side.  Precondition `Root = { "root" }`; postcondition
  `PathBF = π[1, 2] (σ[#0 = #1] (MPath × Res))`.

  Expected verdict: valid.  The demand set is closed under the
  edges out of the seed, so the demanded answers of the
  transformed program are exactly the closure rows whose source
  is demanded (the two containments of Example2004 joined into
  one equality).

  Expected obstruction: rate mismatch.  The executor's round n
  holds, for every source, the pairs joined by at most n+1
  edges; the transformed program reaches a source only when the
  demand reaches it and then builds that source's rows from the
  short ones up, so a source at distance d from the seed has its
  rows of length l only after about d+l rounds.  The containment
  `PathBF ⊆ MPath ⋈ Res` holds round by round, the reverse one
  does not, and no first-order invariant over the current states
  gives the equality (a leveled-framework target; with the final
  values as prophecy constants both directions follow from the
  fixpoint facts of the two loops, with no appeal to leastness).
  It differs from Example2004 by the engine on side 2, the
  PostgreSQL executor (frontier rounds with the already-seen
  check) instead of the naive compiled program, and by the
  claim, an equality with the demand join instead of the pair of
  containments.

  Why a database audience cares: magic sets are how Datalog
  engines push a bound argument into a recursion (Soufflé's
  --magic-transform), while SQL engines evaluate the whole
  recursive view and filter afterwards; the claim says the
  demand-driven answers are exactly what the bulk evaluation
  returns for the same source, the correctness obligation of
  the transformation, stated against the executor's actual
  rounds.

  Sources: souffle-lang/souffle master (commit a1303be3c016,
  2026-07-13): src/ast/transform/MagicSet.cpp, read 2026-09-15;
  souffle-lang.github.io, pages/docs/magicset.md (the
  three stages: constraint normalisation, adornment with the
  SIPS, the magic-rule algorithm), read 2026-09-15.
  postgres/postgres master (commit 6e58d6356fcb, 2026-09-15):
  src/backend/executor/nodeRecursiveunion.c
  `ExecRecursiveUnion`, read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5033

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Root, MPath, MPath_aux} (arity: 1),
    {Edge, PathBF, PathBF_aux, Res, WorkT, Inter} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (Root = { "root" })
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      MPath_aux := ∅[1];
      PathBF_aux := ∅[2];
      MPath := (Root ∪ π[2] (σ[#0 = #1] ((MPath_aux × Edge))));
      PathBF := (π[0,2] (σ[#0 = #1] ((MPath_aux × Edge))) ∪ π[0,4] (σ[(#0 = #1 ∧ #2 = #3)] ((MPath_aux × (Edge × PathBF_aux)))));
      WHILE (¬(((MPath = MPath_aux) ∧ (PathBF = PathBF_aux)))) DO
        MPath_aux := MPath;
        PathBF_aux := PathBF;
        MPath := (MPath ∪ (Root ∪ π[2] (σ[#0 = #1] ((MPath_aux × Edge)))));
        PathBF := (PathBF ∪ (π[0,2] (σ[#0 = #1] ((MPath_aux × Edge))) ∪ π[0,4] (σ[(#0 = #1 ∧ #2 = #3)] ((MPath_aux × (Edge × PathBF_aux))))))
      END;
      Res := Edge;
      WorkT := Edge;
      WHILE (WorkT ≠ ∅) DO
        Inter := ((π[0, 3] (σ[#1 = #2] (Edge × WorkT))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (PathBF = (π[1, 2] (σ[#0 = #1] (MPath × Res))))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5033
end Benchmark
end Whiel
