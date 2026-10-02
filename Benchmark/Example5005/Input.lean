-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Incremental view maintenance against recomputation, the
  direct form of legacy Example2011.

  Inputs `Roots` (unary), `EBase` and `EDelta` (binary): the
  old edge relation and an inserted delta.

  Program 1 (compiled) computes the old view
    `ReachOld(x) :- Roots(x)`
    `ReachOld(y) :- ReachOld(x), EBase(x, y)`
  Program 2, the incremental maintainer (legacy Example2025),
  restarts from `ReachOld ∪ Roots` and iterates over
  `EBase ∪ EDelta`: an insert-only re-evaluation from the old
  view, with Differential Dataflow and Materialize as the setting
  rather than the algorithm encoded.  Program 3 (compiled) recomputes from
  scratch over the new graph
    `ReachNew(x) :- Roots(x)`
    `ReachNew(y) :- ReachNew(x), EBase(x, y)`
    `ReachNew(y) :- ReachNew(x), EDelta(x, y)`

  Program 2 reads program 1's output, so the sequence is
  dependent.  Precondition `true`; postcondition
  `Reach = ReachNew`.  Example2011 instead assumes the old
  view through a closure hypothesis and bounds the result by
  a witness; computing the old view is what makes the
  equality true (a merely closed `ReachOld` could carry junk).

  Expected verdict: valid.
-/

namespace Whiel
namespace Benchmark
namespace Example5005

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Roots, ReachOld, ReachOld_aux, Reach, Reach_2, ReachNew, ReachNew_aux} (arity: 1), {EBase, EDelta} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      ReachOld_aux := ∅[1];
      ReachOld := (Roots ∪ π[2] (σ[#0 = #1] ((ReachOld_aux × EBase))));
      WHILE (¬((ReachOld = ReachOld_aux))) DO
        ReachOld_aux := ReachOld;
        ReachOld := (ReachOld ∪ (Roots ∪ π[2] (σ[#0 = #1] ((ReachOld_aux × EBase)))))
      END;
      Reach_2 := ∅[1];
      Reach := (ReachOld ∪ Roots);
      WHILE (Reach ≠ Reach_2) DO
        Reach_2 := Reach;
        Reach := ((Roots ∪ ReachOld) ∪ (π[1] (σ[#0 = #2] ((EBase ∪ EDelta) × Reach_2))))
      END;
      ReachNew_aux := ∅[1];
      ReachNew := (Roots ∪ (π[2] (σ[#0 = #1] ((ReachNew_aux × EBase))) ∪ π[2] (σ[#0 = #1] ((ReachNew_aux × EDelta)))));
      WHILE (¬((ReachNew = ReachNew_aux))) DO
        ReachNew_aux := ReachNew;
        ReachNew := (ReachNew ∪ (Roots ∪ (π[2] (σ[#0 = #1] ((ReachNew_aux × EBase))) ∪ π[2] (σ[#0 = #1] ((ReachNew_aux × EDelta))))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (Reach = ReachNew)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5005
end Benchmark
end Whiel
