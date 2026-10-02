-- Benchmark contributors: Leo Zhang, Val Tannen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Walks through good vertices and a reformulation over two
  conjunctive views.

  Global schema `{E, G}`: `E` is the digraph edge relation
  and the unary `G` marks the "good" vertices. The global
  query returns the endpoints of a walk of length at least
  two whose interior vertices are all good:
    `T(x, y) :- E(x, z), G(z), E(z, y)`
    `T(x, y) :- E(x, z), G(z), T(z, y)`

  Local schema `{Vb, Ve}`, the two conjunctive views
    `Vb(x, y) ↔ G(x) ∧ E(x, y)`
    `Ve(x, y) ↔ E(x, y) ∧ G(y)`
  with the proposed reformulation
    `T↑(x, y) :- Ve(x, z), Vb(z, y)`
    `T↑(x, y) :- Ve(x, z), T↑(z, y)`

  The command is the two compiled programs run one after
  the other, and `T_aux` and `TUp_aux` are the snapshots
  the compiler generates. The single loop the tool verifies
  is computed from this sequence by the generic
  preprocessor.

  The precondition is the pair of view equations. The
  postcondition is the claim that the two programs agree,
  `T = T↑`.

  Expected verdict: valid. Substituting the view
  definitions turns each `T↑` rule into the matching `T`
  rule, so the two least fixpoints coincide.
-/

namespace Whiel
namespace Benchmark
namespace Example4035

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, T, Vb, Ve, TUp, T_aux, TUp_aux} (arity: 2),
    {G} (arity: 1)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((Vb = (π[1, 2] (σ[#0 = #1] (G × E)))) ∧
      (Ve = (π[0, 1] (σ[#1 = #2] (E × G)))))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T_aux := ∅[2];
      T :=
        ((π[0, 4]
            (σ[(#1 = #2 ∧ #1 = #3)] (E × (G × E)))) ∪
          (π[0, 4]
            (σ[(#1 = #2 ∧ #1 = #3)]
              (E × (G × T_aux)))));
      WHILE (¬ (T = T_aux)) DO
        T_aux := T;
        T :=
          (T ∪
            ((π[0, 4]
                (σ[(#1 = #2 ∧ #1 = #3)]
                  (E × (G × E)))) ∪
              (π[0, 4]
                (σ[(#1 = #2 ∧ #1 = #3)]
                  (E × (G × T_aux))))))
      END;
      TUp_aux := ∅[2];
      TUp :=
        ((π[0, 3] (σ[#1 = #2] (Ve × Vb))) ∪
          (π[0, 3] (σ[#1 = #2] (Ve × TUp_aux))));
      WHILE (¬ (TUp = TUp_aux)) DO
        TUp_aux := TUp;
        TUp :=
          (TUp ∪
            ((π[0, 3] (σ[#1 = #2] (Ve × Vb))) ∪
              (π[0, 3]
                (σ[#1 = #2] (Ve × TUp_aux)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (T = TUp)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example4035
end Benchmark
end Whiel
