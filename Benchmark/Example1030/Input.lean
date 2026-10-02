-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  GPT benchmark Example0011: Foreign-key support core for sharded
  materialized rows.

  Rows are pairs (id, shard) in Base; Req(id, ref) says row id
  needs row ref to exist in the same shard. The loop repeatedly
  removes rows with an unmet requirement (Bad) until none remain,
  so Keep is the greatest subset of Base in which every
  requirement is satisfied within the subset: the greatest fixpoint
  of G(X) = X ∖ Bad(X).

  Strengthened 2026-09-15: the original postcondition only said
  Keep ⊆ Base ∧ Bad = ∅. Rb is a free relation the program never
  touches; the precondition says Rb ⊆ Base is a post-fixpoint of
  G (no row of Rb has an unmet requirement within Rb), and the
  postcondition adds Rb ⊆ Keep. Since Rb ranges over all such
  sets, this asserts maximality: Keep is the greatest consistent
  subset. The legacy certificate covers the original weaker
  claim only.


  Canonical form of the earlier single-level encoding of this case:
  the same schema, precondition, command and postcondition; the
  snapshot relation Keep_2 is now Keep_aux.

  Datalog program(s) recorded for this case:
  * Datalog reading of the greatest-fixpoint integrity core (written for this report; complement formulation: Keep = Base ∖ Removed, a row is removed when a requirement points outside the kept rows of its shard) (hand-written reading (report)):
      Removed(id, s) :- Base(id, s), Req(id, ref), not Base(ref, s).
      Removed(id, s) :- Base(id, s), Req(id, ref), Removed(ref, s).
      Keep(id, s) :- Base(id, s), not Removed(id, s).
-/

namespace Whiel
namespace Benchmark
namespace Example1030

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Base, Req, Keep, Keep_aux, Bad, Rb} (arity: 2),
    {Need, Good, BadNeed} (arity: 3)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (Rb ⊆ Base) ∧ (Rb ⊆ (Rb ∖ (π[0, 1] ((π[0, 1, 3] (σ[#0 = #2] (Rb × Req))) ∖ (π[0, 1, 2] (σ[(#2 = #3) ∧ (#1 = #4)] ((π[0, 1, 3] (σ[#0 = #2] (Rb × Req))) × Rb)))))))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Keep_aux := Base;
      Need := (π[0, 1, 3] (σ[#0 = #2] (Keep_aux × Req)));
      Good := (π[0, 1, 2] (σ[(#2 = #3) ∧ (#1 = #4)] (Need × Keep_aux)));
      BadNeed := (Need ∖ Good);
      Bad := (π[0, 1] BadNeed);
      Keep := (Keep_aux ∖ Bad);
      WHILE Keep ≠ Keep_aux DO
      Keep_aux := Keep;
      Need := (π[0, 1, 3] (σ[#0 = #2] (Keep_aux × Req)));
      Good := (π[0, 1, 2] (σ[(#2 = #3) ∧ (#1 = #4)] (Need × Keep_aux)));
      BadNeed := (Need ∖ Good);
      Bad := (π[0, 1] BadNeed);
      Keep := (Keep_aux ∖ Bad)
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((Keep ⊆ Base) ∧ (Bad = ∅[2])) ∧ (Rb ⊆ Keep)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example1030
end Benchmark
end Whiel
