-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Soufflé's `family` benchmark program evaluated naively and
  semi-naively, tested for equality of every output.

  Both sides are script-generated translations of the
  normalized Soufflé source (the naive form is the
  fixed-point program, the semi-naive form uses classical
  frontier evaluation derived from the same source).  Side
  2's relations carry the suffix `S`. Outputs compared:
  ancestor, cousin, grandmother, parent, relative, sibling.

  Independent programs, merged side by side.  Precondition
  `true`; postcondition: each output equals its `S` twin.

  Expected verdict: valid: naive and semi-naive evaluation
  compute the same least fixpoints, and non-recursive
  outputs are computed by identical straight-line code on
  both sides.
-/

namespace Whiel
namespace Benchmark
namespace Example5009

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {father, mother, ancestor, cousin, grandmother, parent, relative, sibling, ancestorNew, ancestorOld, ancestorS, cousinS, grandmotherS, parentS, relativeS, siblingS, deltaAncestorS} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      parent := ((π[0, 1] father) ∪ (π[0, 1] mother));
      sibling := (π[1, 3] (σ[(#2 = #0 ∧ ¬(#1 = #3))] (parent × parent)));
      relative := (π[0, 3] (σ[#2 = #1] (sibling × parent)));
      ancestorNew := (π[0, 1] parent);
      ancestorOld := ∅[2];
      WHILE (ancestorNew ≠ ancestorOld) DO
      ancestorOld := ancestorNew;
      ancestorNew := (ancestorNew ∪ (π[0, 3] (σ[#2 = #1] (parent × ancestorOld))))
      END;
      ancestor := ancestorNew;
      cousin := (π[1, 3] (((σ[(#2 = #0 ∧ ¬(#1 = #3))] (ancestor × ancestor)) ∖ (π[0, 1, 2, 3] (σ[(#4 = #1 ∧ #5 = #3)] ((σ[(#2 = #0 ∧ ¬(#1 = #3))] (ancestor × ancestor)) × sibling)))) ∖ (π[0, 1, 2, 3] (σ[(#4 = #1 ∧ #5 = #3)] (((σ[(#2 = #0 ∧ ¬(#1 = #3))] (ancestor × ancestor)) ∖ (π[0, 1, 2, 3] (σ[(#4 = #1 ∧ #5 = #3)] ((σ[(#2 = #0 ∧ ¬(#1 = #3))] (ancestor × ancestor)) × sibling)))) × parent)))));
      grandmother := (π[0, 3] (σ[#2 = #1] (mother × ancestor)));
      parentS := ((π[0, 1] father) ∪ (π[0, 1] mother));
      siblingS := (π[1, 3] (σ[(#2 = #0 ∧ ¬(#1 = #3))] (parentS × parentS)));
      relativeS := (π[0, 3] (σ[#2 = #1] (siblingS × parentS)));
      ancestorS := ∅[2];
      deltaAncestorS := (π[0, 1] parentS);
      WHILE (deltaAncestorS ≠ ∅[2]) DO
      ancestorS := (ancestorS ∪ deltaAncestorS);
      deltaAncestorS := ((π[0, 3] (σ[#2 = #1] (parentS × deltaAncestorS))) ∖ ancestorS)
      END;
      cousinS := (π[1, 3] (((σ[(#2 = #0 ∧ ¬(#1 = #3))] (ancestorS × ancestorS)) ∖ (π[0, 1, 2, 3] (σ[(#4 = #1 ∧ #5 = #3)] ((σ[(#2 = #0 ∧ ¬(#1 = #3))] (ancestorS × ancestorS)) × siblingS)))) ∖ (π[0, 1, 2, 3] (σ[(#4 = #1 ∧ #5 = #3)] (((σ[(#2 = #0 ∧ ¬(#1 = #3))] (ancestorS × ancestorS)) ∖ (π[0, 1, 2, 3] (σ[(#4 = #1 ∧ #5 = #3)] ((σ[(#2 = #0 ∧ ¬(#1 = #3))] (ancestorS × ancestorS)) × siblingS)))) × parentS)))));
      grandmotherS := (π[0, 3] (σ[#2 = #1] (mother × ancestorS)))
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((ancestor = ancestorS) ∧ (cousin = cousinS) ∧ (grandmother = grandmotherS) ∧ (parent = parentS) ∧ (relative = relativeS) ∧ (sibling = siblingS))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5009
end Benchmark
end Whiel
