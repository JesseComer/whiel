-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  equivalence_03:
  Frontier (grey-set) marking ≡ naive mark propagation.

  Pair: reachability_11 (Go runtime GC mark phase,
  src/runtime/mgcmark.go - gcDrain/scanobject/greyobject
  with an explicit grey frontier and marked-check dedup)
  against naive whole-set re-propagation (the strategy of
  HotSpot's ConnectionGraph escape propagation,
  reachability_03).

  Method (equ.pdf): run the frontier program only, framed by
  a fresh relation RBound constrained to be a pre-fixpoint
  of the naive operator
      F1(X) = RootPtr ∪ img(HeapPtr, X).
  The postcondition asserts Marked is a pre-fixpoint of F1
  and Marked ⊆ RBound, so Marked = lfp(F1): frontier-based
  marking with the greyobject "if marked we have nothing to
  do" dedup marks exactly the objects naive re-scanning
  marks.  The invariant must carry the frontier law that
  pointees of Marked ∖ Grey are already Marked.


  Canonical form of the earlier single-level encoding of this
  case: the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * prog_p (production check):
      MarkedC(x1) :- RootPtr(x1).
      MarkedC(y1) :- MarkedC(x1), HeapPtr(x1, y1).
-/

namespace Whiel
namespace Benchmark
namespace Example2012

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {RootPtr, Marked, Grey, NewG, RBound} (arity: 1),
    {HeapPtr} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((RootPtr ∪ (π[1] (σ[#0 = #2] (HeapPtr × RBound)))) ⊆ RBound)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Marked := RootPtr;
      Grey := RootPtr;
      WHILE Grey ≠ ∅ DO
        NewG := ((π[1] (σ[#0 = #2] (HeapPtr × Grey))) ∖ Marked);
        Marked := (Marked ∪ NewG);
        Grey := NewG
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((RootPtr ∪ (π[1] (σ[#0 = #2] (HeapPtr × Marked)))) ⊆ Marked) ∧
    (Marked ⊆ RBound)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example2012
end Benchmark
end Whiel
