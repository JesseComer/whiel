-- Benchmark contributors: Leo Zhang, Val Tannen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  A directed-triangle query and its reformulation over a
  length-two path view.

  Global schema `{E}` (binary), the edges of a digraph. The
  global query returns the vertices that start a directed
  triangle:
    `Q(x) :- E(x, y), E(y, z), E(z, x)`

  Local schema `{V}` (ternary), a view that records a
  length-two path together with its midpoint. The proposed
  reformulation joins two copies of that view on
  overlapping variables:
    `Q↑(x) :- V(x, y, z), V(y, z, x)`

  The command is the two compiled programs run one after
  the other, and `Q_aux` and `QUp_aux` are the snapshots
  the compiler generates. The single loop the tool verifies
  is computed from this sequence by the generic
  preprocessor.

  The precondition is the view constraint `V = E ∘ E` with
  the midpoint kept. The postcondition is the claim that
  the two queries agree, `Q = Q↑`.

  Expected verdict: valid. A directed triangle through `x`
  is exactly a pair of length-two paths that wrap around,
  so joining the view with itself rebuilds the query under
  set semantics.
-/

namespace Whiel
namespace Benchmark
namespace Example4001

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Q, QUp, Q_aux, QUp_aux} (arity: 1),
    {E} (arity: 2),
    {V} (arity: 3)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (V = (π[0, 1, 3] (σ[#1 = #2] (E × E))))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Q_aux := ∅[1];
      Q :=
        (π[0]
          (σ[((#1 = #2 ∧ #3 = #4) ∧ #0 = #5)]
            (E × (E × E))));
      WHILE (¬ (Q = Q_aux)) DO
        Q_aux := Q;
        Q :=
          (Q ∪
            (π[0]
              (σ[((#1 = #2 ∧ #3 = #4) ∧ #0 = #5)]
                (E × (E × E)))))
      END;
      QUp_aux := ∅[1];
      QUp :=
        (π[0]
          (σ[((#1 = #3 ∧ #2 = #4) ∧ #0 = #5)]
            (V × V)));
      WHILE (¬ (QUp = QUp_aux)) DO
        QUp_aux := QUp;
        QUp :=
          (QUp ∪
            (π[0]
              (σ[((#1 = #3 ∧ #2 = #4) ∧ #0 = #5)]
                (V × V))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (Q = QUp)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example4001
end Benchmark
end Whiel
