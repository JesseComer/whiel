-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Soufflé's `orbits` benchmark program evaluated naively and
  semi-naively, tested for equality of every output.

  Both sides are script-generated translations of the
  normalized Soufflé source (the naive form is the
  fixed-point program, the semi-naive form uses classical
  frontier evaluation derived from the same source).  Side
  2's relations carry the suffix `S`. Outputs compared:
  intermediate, orbits, satellite.

  Independent programs, merged side by side.  Precondition
  `true`; postcondition: each output equals its `S` twin.

  Expected verdict: valid: naive and semi-naive evaluation
  compute the same least fixpoints, and non-recursive
  outputs are computed by identical straight-line code on
  both sides.
-/

namespace Whiel
namespace Benchmark
namespace Example5010

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {orbitsSeed, intermediate, orbits, satellite, orbitsNew, orbitsOld, intermediateS, orbitsS, satelliteS, deltaOrbitsS} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      orbitsNew := (π[0, 1] orbitsSeed);
      orbitsOld := ∅[2];
      WHILE (orbitsNew ≠ orbitsOld) DO
      orbitsOld := orbitsNew;
      orbitsNew := (orbitsNew ∪ (π[0, 3] (σ[#2 = #1] (orbitsOld × orbitsOld))))
      END;
      orbits := orbitsNew;
      intermediate := (π[0, 3] (σ[#2 = #1] (orbits × orbits)));
      satellite := (π[0, 1] (orbits ∖ (π[0, 1] (σ[(#2 = #0 ∧ #3 = #1)] (orbits × intermediate)))));
      orbitsS := ∅[2];
      deltaOrbitsS := (π[0, 1] orbitsSeed);
      WHILE (deltaOrbitsS ≠ ∅[2]) DO
      orbitsS := (orbitsS ∪ deltaOrbitsS);
      deltaOrbitsS := ((((π[0, 3] (σ[#2 = #1] (deltaOrbitsS × orbitsS))) ∪ (π[0, 3] (σ[#2 = #1] (orbitsS × deltaOrbitsS)))) ∪ (π[0, 3] (σ[#2 = #1] (deltaOrbitsS × deltaOrbitsS)))) ∖ orbitsS)
      END;
      intermediateS := (π[0, 3] (σ[#2 = #1] (orbitsS × orbitsS)));
      satelliteS := (π[0, 1] (orbitsS ∖ (π[0, 1] (σ[(#2 = #0 ∧ #3 = #1)] (orbitsS × intermediateS)))))
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((intermediate = intermediateS) ∧ (orbits = orbitsS) ∧ (satellite = satelliteS))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5010
end Benchmark
end Whiel
