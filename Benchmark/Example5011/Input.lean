-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Soufflé's `topological_ordering` benchmark program evaluated naively and
  semi-naively, tested for equality of every output.

  Both sides are script-generated translations of the normalized Soufflé
  source (the naive form is the fixed-point program, the semi-naive form
  uses classical frontier evaluation derived from the same source).  Side
  2's relations carry the suffix `S`. Outputs compared: hasSuccessorRank,
  index, indices, isAfter, isBefore, isolated, source, vertex.

  Independent programs, merged side by side.  Precondition
  `true`; postcondition: each output equals its `S` twin.

  Expected verdict: invalid. The recorded counterexample
  refutes equality of the two translated programs on this
  unconstrained input domain; Certificate/Invalid.lean
  proves the negation of this exact Hoare triple.
-/

namespace Whiel
namespace Benchmark
namespace Example5011

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {RankOne, RankZero, isolated, source, vertex, isolatedS, sourceS, vertexS} (arity: 1),
    {Succ, edge, hasSuccessorRank, index, indices, isAfter, isBefore, indicesNew, indicesOld, isAfterNew, isAfterOld, isBeforeNew, isBeforeOld, hasSuccessorRankS, indexS, indicesS, isAfterS, isBeforeS, deltaIndicesS, deltaIndicesOldS, deltaIsAfterS, deltaIsAfterOldS, deltaIsBeforeS, deltaIsBeforeOldS} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      vertex := ((π[0] edge) ∪ (π[1] edge));
      isolated := (π[0] ((vertex ∖ (π[0] (σ[#2 = #0] (vertex × edge)))) ∖ (π[0] (σ[#1 = #0] ((vertex ∖ (π[0] (σ[#2 = #0] (vertex × edge)))) × edge)))));
      source := (π[0] ((σ[#1 = #0] (vertex × edge)) ∖ (π[0, 1, 2] (σ[#4 = #0] ((σ[#1 = #0] (vertex × edge)) × edge)))));
      indicesNew := ((π[0, 1] (isolated × RankZero)) ∪ (π[0, 1] (source × RankOne)));
      indicesOld := ∅[2];
      isAfterNew := (π[1, 0] edge);
      isAfterOld := ∅[2];
      isBeforeNew := (π[0, 1] edge);
      isBeforeOld := ∅[2];
      WHILE (((indicesNew ≠ indicesOld) ∨ (isAfterNew ≠ isAfterOld)) ∨ (isBeforeNew ≠ isBeforeOld)) DO
      indicesOld := indicesNew;
      isAfterOld := isAfterNew;
      isBeforeOld := isBeforeNew;
      indicesNew := (indicesNew ∪ (π[0, 5] (σ[(#2 = #1 ∧ #4 = #3)] ((isAfterOld × indicesOld) × Succ))));
      isAfterNew := (isAfterNew ∪ (π[1, 2] (σ[#3 = #0] (isAfterOld × isAfterOld))));
      isBeforeNew := (isBeforeNew ∪ (π[0, 3] (σ[#2 = #1] (isBeforeOld × isBeforeOld))))
      END;
      indices := indicesNew;
      isAfter := isAfterNew;
      isBefore := isBeforeNew;
      hasSuccessorRank := (π[0, 1] (σ[((#2 = #1 ∧ #4 = #0) ∧ #5 = #3)] ((indices × Succ) × indices)));
      index := (π[0, 1] (indices ∖ (π[0, 1] (σ[(#2 = #0 ∧ #3 = #1)] (indices × hasSuccessorRank)))));
      vertexS := ((π[0] edge) ∪ (π[1] edge));
      isolatedS := (π[0] ((vertexS ∖ (π[0] (σ[#2 = #0] (vertexS × edge)))) ∖ (π[0] (σ[#1 = #0] ((vertexS ∖ (π[0] (σ[#2 = #0] (vertexS × edge)))) × edge)))));
      sourceS := (π[0] ((σ[#1 = #0] (vertexS × edge)) ∖ (π[0, 1, 2] (σ[#4 = #0] ((σ[#1 = #0] (vertexS × edge)) × edge)))));
      indicesS := ∅[2];
      deltaIndicesS := ((π[0, 1] (isolatedS × RankZero)) ∪ (π[0, 1] (sourceS × RankOne)));
      deltaIndicesOldS := ∅[2];
      isAfterS := ∅[2];
      deltaIsAfterS := (π[1, 0] edge);
      deltaIsAfterOldS := ∅[2];
      isBeforeS := ∅[2];
      deltaIsBeforeS := (π[0, 1] edge);
      deltaIsBeforeOldS := ∅[2];
      WHILE (((deltaIndicesS ≠ ∅[2]) ∨ (deltaIsAfterS ≠ ∅[2])) ∨ (deltaIsBeforeS ≠ ∅[2])) DO
      deltaIndicesOldS := deltaIndicesS;
      deltaIsAfterOldS := deltaIsAfterS;
      deltaIsBeforeOldS := deltaIsBeforeS;
      indicesS := (indicesS ∪ deltaIndicesOldS);
      isAfterS := (isAfterS ∪ deltaIsAfterOldS);
      isBeforeS := (isBeforeS ∪ deltaIsBeforeOldS);
      deltaIndicesS := ((π[0, 5] (σ[(#2 = #1 ∧ #4 = #3)] ((isAfterS × deltaIndicesOldS) × Succ))) ∖ indicesS);
      deltaIsAfterS := ((((π[1, 2] (σ[#3 = #0] (deltaIsAfterOldS × isAfterS))) ∪ (π[1, 2] (σ[#3 = #0] (isAfterS × deltaIsAfterOldS)))) ∪ (π[1, 2] (σ[#3 = #0] (deltaIsAfterOldS × deltaIsAfterOldS)))) ∖ isAfterS);
      deltaIsBeforeS := ((((π[0, 3] (σ[#2 = #1] (deltaIsBeforeOldS × isBeforeS))) ∪ (π[0, 3] (σ[#2 = #1] (isBeforeS × deltaIsBeforeOldS)))) ∪ (π[0, 3] (σ[#2 = #1] (deltaIsBeforeOldS × deltaIsBeforeOldS)))) ∖ isBeforeS)
      END;
      hasSuccessorRankS := (π[0, 1] (σ[((#2 = #1 ∧ #4 = #0) ∧ #5 = #3)] ((indicesS × Succ) × indicesS)));
      indexS := (π[0, 1] (indicesS ∖ (π[0, 1] (σ[(#2 = #0 ∧ #3 = #1)] (indicesS × hasSuccessorRankS)))))
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((hasSuccessorRank = hasSuccessorRankS) ∧ (index = indexS) ∧ (indices = indicesS) ∧ (isAfter = isAfterS) ∧ (isBefore = isBeforeS) ∧ (isolated = isolatedS) ∧ (source = sourceS) ∧ (vertex = vertexS))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5011
end Benchmark
end Whiel
