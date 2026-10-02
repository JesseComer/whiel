-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  OpenFGA's two evaluation directions for one question,
  membership of users in groups through nested usersets: Check,
  which descends from the object, and ListObjects, which ascends
  from the user by reverse expansion.

  Model `type group, define member: [user, group#member]`.
  Inputs `DirectMember(u, g)` (the tuple group:g#member@user:u)
  and `SubGroup(h, g)` (the tuple group:g#member@group:h#member:
  the members of h are members of g), both binary; `QUser(u)`
  and `Query(g)`, unary, the users and objects asked about.
  The membership program is
    `Member(u, g) :- DirectMember(u, g)`
    `Member(u, g) :- Member(u, h), SubGroup(h, g)`
  (the program of legacy Example2032, the bottom-up reference
  on the check instances).

  Side 1, Check (internal/graph/check.go, read 2026-09-15):
  `checkDirect` is the union of `checkDirectUserTuple` (the
  direct tuple) and `checkDirectUsersetTuples`, whose default
  strategy (`defaultUserset`) reads the userset tuples
  group:g#member@group:h#member of the object and dispatches
  Check(user, group:h#member) for each; `ResolveCheck` stops a
  path at `maxResolutionDepth` and on a repeated tuple key
  (`hasCycle`).  Set-at-a-time over the queried pairs this is
  the demand-driven form of the membership program:
    `Demand(g) :- Query(g)`
    `Demand(h) :- Demand(g), SubGroup(h, g)`
    `Ans(u, g) :- Demand(g), QUser(u), DirectMember(u, g)`
    `Ans(u, g) :- Demand(g), SubGroup(h, g), Ans(u, h)`
  compiled by the naive compiler; `Demand_aux` and `Ans_aux` are
  its snapshots.  (The planner may instead pick the recursive
  fast path of internal/graph/recursive_resolver.go, which loads
  the usersets the user belongs to and walks breadth-first from
  the object until a level meets them; that one-phase strategy
  is not the side modelled here.)

  Side 2, ListObjects (pkg/server/commands/reverseexpand/
  reverse_expand.go and pkg/server/commands/list_objects.go,
  read 2026-09-15): `execute` takes the source user:u, asks the
  type system for the edges into group#member
  (`GetPrunedRelationshipEdges`) and, on the direct edge,
  `readTuplesAndExecute` runs `ReadStartingWithUser` for the
  tuples group:g#member@user:u; each object found becomes the
  source userset group:g#member of a new `execute`, which emits g
  as a candidate (`trySendCandidate`, deduplicated) and reads the
  tuples group:g2#member@group:g#member in turn;
  `visitedUsersetsMap` stops cycles and `resolveNodeLimit` bounds
  the depth.  With no intersection or exclusion on the path the
  candidates are results without a further Check
  (list_objects.go `evaluate`, `NoFurtherEvalStatus`).
  Set-at-a-time:
    `Reach(u, g) :- QUser(u), DirectMember(u, g)`
    `Reach(u, g) :- Reach(u, h), SubGroup(h, g)`
  compiled by the naive compiler; `Reach_aux` is its snapshot.

  The two programs write disjoint relations and are merged side
  by side.  Precondition `true`; postcondition
  `π[0, 1] (σ[#1 = #2] (Ans × Query)) = π[0, 1] (σ[#1 = #2] (Reach × Query))`,
  the answers on the queried users and objects.

  Expected verdict: valid.  On a demanded object, `Ans` is the
  membership of the queried users; from a queried user, `Reach`
  is the membership on every object; both restrict to the
  queried pairs.

  Expected obstruction: rate mismatch.  Reverse expansion climbs
  one subgroup level per round from the user's direct groups, so
  a queried group at height n above them is reached after n
  rounds.  The top-down check first propagates the demand down n
  levels and only then builds the answers back up, one level per
  round, so the same pair is answered after about 2n rounds. The
  gap grows with n, and no first-order invariant over the current
  states relates the two frontiers (a leveled-framework target,
  as Example5033); with the final values as prophecy constants
  both containments follow from the fixpoint facts of the two
  loops, with no appeal to leastness.

  Why a database audience cares: a relationship-based
  authorization store answers "may u access g" by descending
  from the object and "which g may u access" by ascending from
  the user; the two are the top-down and the bottom-up
  evaluation of one recursive query, and the claim that they
  agree on the common questions is what lets one be served, or
  validated, by the other.  It replaces the legacy correctness
  case Example2032, whose bottom-up loop is the reference
  program here.

  Sources: openfga/openfga main (commit 73591ef16ce5,
  2026-09-08): internal/graph/check.go (`checkDirect`,
  `checkDirectUserTuple`, `checkDirectUsersetTuples`,
  `ResolveCheck`, `hasCycle`), internal/graph/
  recursive_resolver.go (`recursiveFastPath`,
  `breadthFirstRecursiveMatch`), pkg/server/commands/
  reverseexpand/reverse_expand.go (`execute`,
  `reverseExpandDirect`, `readTuplesAndExecute`,
  `trySendCandidate`), pkg/server/commands/list_objects.go
  (`evaluate`); all read 2026-09-15.
-/

namespace Whiel
namespace Benchmark
namespace Example5038

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Query, QUser, Demand, Demand_aux} (arity: 1),
    {DirectMember, SubGroup, Ans, Ans_aux, Reach, Reach_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    true
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Demand_aux := ∅[1];
      Ans_aux := ∅[2];
      Demand := (Query ∪ π[1] (σ[#0 = #2] ((Demand_aux × SubGroup))));
      Ans := (π[1,0] (σ[(#1 = #2 ∧ #0 = #3)] ((Demand_aux × (QUser × DirectMember)))) ∪ π[3,0] (σ[(#0 = #2 ∧ #1 = #4)] ((Demand_aux × (SubGroup × Ans_aux)))));
      WHILE (¬(((Demand = Demand_aux) ∧ (Ans = Ans_aux)))) DO
        Demand_aux := Demand;
        Ans_aux := Ans;
        Demand := (Demand ∪ (Query ∪ π[1] (σ[#0 = #2] ((Demand_aux × SubGroup)))));
        Ans := (Ans ∪ (π[1,0] (σ[(#1 = #2 ∧ #0 = #3)] ((Demand_aux × (QUser × DirectMember)))) ∪ π[3,0] (σ[(#0 = #2 ∧ #1 = #4)] ((Demand_aux × (SubGroup × Ans_aux))))))
      END;
      Reach_aux := ∅[2];
      Reach := (π[0,2] (σ[#0 = #1] ((QUser × DirectMember))) ∪ π[0,3] (σ[#1 = #2] ((Reach_aux × SubGroup))));
      WHILE (¬((Reach = Reach_aux))) DO
        Reach_aux := Reach;
        Reach := (Reach ∪ (π[0,2] (σ[#0 = #1] ((QUser × DirectMember))) ∪ π[0,3] (σ[#1 = #2] ((Reach_aux × SubGroup)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((π[0, 1] (σ[#1 = #2] (Ans × Query))) = (π[0, 1] (σ[#1 = #2] (Reach × Query))))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5038
end Benchmark
end Whiel
