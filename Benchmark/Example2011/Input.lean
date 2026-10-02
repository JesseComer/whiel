-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  equivalence_02:
  Incremental view maintenance ≡ from-scratch
  recomputation.

  Pair: reachability_05 (Differential Dataflow / Materialize
  incremental reachability, restarted from the previously
  maintained view) against from-scratch reachability over
  the updated edge set EBase ∪ EDelta.

  Method (equ.pdf): run the incremental program only, framed
  by a fresh relation RBound constrained to be a
  pre-fixpoint of the from-scratch operator
      F1(X) = Roots ∪ img(EBase ∪ EDelta, X).
  The precondition also carries the incrementality
  hypothesis: ReachOld is a pre-fixpoint of the old operator
  (over EBase alone), and - standing in for its minimality,
  which cannot be stated directly - ReachOld ⊆ RBound.
  The postcondition asserts the incremental result is a
  pre-fixpoint of F1 and is contained in RBound; together
  these pin Reach to lfp(F1), i.e. the incremental update
  yields exactly the view a full recomputation would - the
  core guarantee of differential dataflow.

  Provenance correction (2026-09-15): the algorithm encoded is
  insert-only re-evaluation restarted from the maintained view
  over EBase ∪ EDelta. Differential Dataflow and Materialize
  propagate timestamped differences and handle deletions; they are
  the setting for the claim (incremental result = recomputation),
  not the algorithm encoded.


  Canonical form of the earlier single-level encoding of this
  case: the same schema, precondition, command and postcondition;
  the snapshot relation Reach_2 is now Reach_aux.

  Datalog program(s) recorded for this case:
  * prog_p (production check):
      ReachC(x1) :- Roots(x1).
      ReachC(x1) :- ReachOld(x1).
      ReachC(y1) :- ReachC(x1), EBase(x1, y1).
      ReachC(y1) :- ReachC(x1), EDelta(x1, y1).
-/

namespace Whiel
namespace Benchmark
namespace Example2011

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Roots, ReachOld, Reach, Reach_aux, RBound} (arity: 1),
    {EBase, EDelta} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((Roots ∪ (π[1] (σ[#0 = #2] (EBase × ReachOld)))) ⊆ ReachOld) ∧
    (((Roots ∪ (π[1] (σ[#0 = #2] ((EBase ∪ EDelta) × RBound)))) ⊆ RBound) ∧
     (ReachOld ⊆ RBound))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Reach_aux := ∅;
      Reach := (ReachOld ∪ Roots);
      WHILE Reach ≠ Reach_aux DO
        Reach_aux := Reach;
        Reach := ((Roots ∪ ReachOld) ∪
          (π[1] (σ[#0 = #2] ((EBase ∪ EDelta) × Reach_aux))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((Roots ∪ (π[1] (σ[#0 = #2] ((EBase ∪ EDelta) × Reach)))) ⊆ Reach) ∧
    (Reach ⊆ RBound)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example2011
end Benchmark
end Whiel
