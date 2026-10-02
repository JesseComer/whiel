-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  equivalence_01:
  Semi-naive evaluation ≡ naive/declarative transitive
  closure.

  Pair: transitive_closure_06 (PostgreSQL
  `ExecRecursiveUnion`, src/backend/executor/
  nodeRecursiveunion.c) against the declarative left-linear
  TC semantics (Soufflé naive evaluation,
  souffle-lang.github.io/translate).

  Method (equ.pdf, §Equivalence): run the semi-naive
  program only, with the working-table seeded by Edge, and
  frame it with a fresh relation RBound that the
  precondition constrains to be a pre-fixpoint of the
  reference operator
      F1(X) = Edge ∪ (X ∘ Edge).
  The postcondition asserts the output Res is itself a
  pre-fixpoint of F1 and is contained in RBound.  Since
  RBound ranges over all pre-fixpoints, Res = lfp(F1):
  the semi-naive loop computes exactly the naive LFP.

  This is the equivalence the equ.pdf text requests
  ("...show that the ... seminaive is equivalent to linear
  transitive closure").  The required invariant must relate
  the frontier WorkT to the accumulated Res (e.g.
  WorkT ⊆ Res, Res ⊆ RBound, and the semi-naive frontier
  law that consequences of Res ∖ WorkT are already in Res).


  Canonical form of the earlier single-level encoding of this
  case: the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * prog_p (production check):
      ResC(x1, y1) :- Edge(x1, y1).
      ResC(x1, z1) :- ResC(x1, y1), Edge(y1, z1).
-/

namespace Whiel
namespace Benchmark
namespace Example2010

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Edge, Res, WorkT, Inter, RBound} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((Edge ∪ (π[0, 3] (σ[#1 = #2] (RBound × Edge)))) ⊆ RBound)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Res := Edge;
      WorkT := Edge;
      WHILE WorkT ≠ ∅ DO
        Inter := ((π[0, 3] (σ[#1 = #2] (WorkT × Edge))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((Edge ∪ (π[0, 3] (σ[#1 = #2] (Res × Edge)))) ⊆ Res) ∧
    (Res ⊆ RBound)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example2010
end Benchmark
end Whiel
