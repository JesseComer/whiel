-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  containment_05:
  E[f U g] is contained in EF g.

  Pair: preimage_fixpoint_01 (NuSMV's eu() frontier loop,
  src/mc/mcMc.c) against the unconstrained backward
  reachability that computes EF g (NuSMV's ef() is
  eu(true, g)).  This is the textbook CTL fact that an
  until-witness is in particular an eventually-witness.

  Method (equ.pdf, §Containment): run the EU program only,
  framed by a fresh relation RBound constrained to be a
  pre-fixpoint of the EF operator
      F1(X) = SatG ∪ pre(Trans, X).
  The postcondition Y ⊆ RBound bounds the EU states by
  lfp(F1) = the EF g states.


  Canonical form of the earlier single-level encoding of this
  case: the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * prog_p (production check):
      YC(x1) :- SatG(x1).
      YC(x1) :- SatF(x1), Trans(x1, y1), YC(y1).
-/

namespace Whiel
namespace Benchmark
namespace Example2007

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {SatF, SatG, Y, Yold, NewS, PreS, RBound} (arity: 1),
    {Trans} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((SatG ∪ (π[0] (σ[#1 = #2] (Trans × RBound)))) ⊆ RBound)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Y := SatG;
      NewS := SatG;
      WHILE NewS ≠ ∅ DO
        Yold := Y;
        PreS := (π[0] (σ[#1 = #2] (Trans × NewS)));
        Y := (Y ∪ (SatF ∖ (SatF ∖ PreS)));
        NewS := (Y ∖ Yold)
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (Y ⊆ RBound)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example2007
end Benchmark
end Whiel
