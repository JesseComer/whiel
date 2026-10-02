-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Soufflé's `tc` benchmark program evaluated naively and
  semi-naively, tested for equality of every output.

  Both sides are script-generated translations of the
  normalized Soufflé source (the naive form is the
  fixed-point program, the semi-naive form uses classical
  frontier evaluation derived from the same source).  Side
  2's relations carry the suffix `S`. Outputs compared: tc,
  tcl, tcr.

  Independent programs, merged side by side.  Precondition
  `true`; postcondition: each output equals its `S` twin.

  Expected verdict: valid: naive and semi-naive evaluation
  compute the same least fixpoints, and non-recursive
  outputs are computed by identical straight-line code on
  both sides.
-/

namespace Whiel
namespace Benchmark
namespace Example5008

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {base, tc, tcl, tcr, tcNew, tcOld, tclNew, tclOld, tcrNew, tcrOld, tcS, tclS, tcrS, deltaTcS, deltaTcOldS, deltaTclS, deltaTclOldS, deltaTcrS, deltaTcrOldS} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      tcNew := (π[0, 1] base);
      tcOld := ∅[2];
      tclNew := (π[0, 1] base);
      tclOld := ∅[2];
      tcrNew := (π[0, 1] base);
      tcrOld := ∅[2];
      WHILE (((tcNew ≠ tcOld) ∨ (tclNew ≠ tclOld)) ∨ (tcrNew ≠ tcrOld)) DO
      tcOld := tcNew;
      tclOld := tclNew;
      tcrOld := tcrNew;
      tcNew := (tcNew ∪ (π[0, 3] (σ[#2 = #1] (tcOld × tcOld))));
      tclNew := (tclNew ∪ (π[0, 3] (σ[#2 = #1] (tclOld × base))));
      tcrNew := (tcrNew ∪ (π[0, 3] (σ[#2 = #1] (base × tcrOld))))
      END;
      tc := tcNew;
      tcl := tclNew;
      tcr := tcrNew;
      tcS := ∅[2];
      deltaTcS := (π[0, 1] base);
      deltaTcOldS := ∅[2];
      tclS := ∅[2];
      deltaTclS := (π[0, 1] base);
      deltaTclOldS := ∅[2];
      tcrS := ∅[2];
      deltaTcrS := (π[0, 1] base);
      deltaTcrOldS := ∅[2];
      WHILE (((deltaTcS ≠ ∅[2]) ∨ (deltaTclS ≠ ∅[2])) ∨ (deltaTcrS ≠ ∅[2])) DO
      deltaTcOldS := deltaTcS;
      deltaTclOldS := deltaTclS;
      deltaTcrOldS := deltaTcrS;
      tcS := (tcS ∪ deltaTcOldS);
      tclS := (tclS ∪ deltaTclOldS);
      tcrS := (tcrS ∪ deltaTcrOldS);
      deltaTcS := ((((π[0, 3] (σ[#2 = #1] (deltaTcOldS × tcS))) ∪ (π[0, 3] (σ[#2 = #1] (tcS × deltaTcOldS)))) ∪ (π[0, 3] (σ[#2 = #1] (deltaTcOldS × deltaTcOldS)))) ∖ tcS);
      deltaTclS := ((π[0, 3] (σ[#2 = #1] (deltaTclOldS × base))) ∖ tclS);
      deltaTcrS := ((π[0, 3] (σ[#2 = #1] (base × deltaTcrOldS))) ∖ tcrS)
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((tc = tcS) ∧ (tcl = tclS) ∧ (tcr = tcrS))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5008
end Benchmark
end Whiel
