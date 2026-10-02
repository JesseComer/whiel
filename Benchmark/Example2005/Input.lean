-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  containment_03:
  Restricted-edge reachability is contained in full-edge
  reachability (edge-monotonicity).

  Pair: reachability_07 (npm Arborist calc-dep-flags.js:
  NonOpt, the nodes reachable through non-optional edges
  only) against reachability_06 (the full reachability that
  determines non-extraneous nodes).  Production meaning:
  every node that keeps a hard dependency path from the
  root is in particular not extraneous.

  Method (equ.pdf, §Containment): run the hard-edge closure
  only, framed by a fresh relation RBound constrained to be
  a pre-fixpoint of the all-edges operator
      F1(X) = RootN ∪ img(EdgeAll, X).
  The postcondition NonOpt ⊆ RBound then bounds the
  hard-edge closure by lfp(F1) = the full reachable set.


  Canonical form of the earlier single-level encoding of this
  case: the same schema, precondition, command and postcondition;
  the snapshot relation NonOpt_2 is now NonOpt_aux.

  Datalog program(s) recorded for this case:
  * prog_p (production check):
      NonOptC(x1) :- RootN(x1).
      NonOptC(y1) :- NonOptC(x1), EdgeHardC(x1, y1).
-/

namespace Whiel
namespace Benchmark
namespace Example2005

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {RootN, NonOpt, NonOpt_aux, RBound} (arity: 1),
    {EdgeAll, EdgeOpt, EdgeHard} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((RootN ∪ (π[1] (σ[#0 = #2] (EdgeAll × RBound)))) ⊆ RBound)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      NonOpt_aux := ∅;
      EdgeHard := (EdgeAll ∖ EdgeOpt);
      NonOpt := RootN;
      WHILE NonOpt ≠ NonOpt_aux DO
        NonOpt_aux := NonOpt;
        NonOpt := (RootN ∪
          (π[1] (σ[#0 = #2] (EdgeHard × NonOpt_aux))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (NonOpt ⊆ RBound)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example2005
end Benchmark
end Whiel
