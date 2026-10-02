-- Benchmark contributors: Leo Zhang, Val Tannen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  An odd/even path program and a reformulation over a
  length-two path view, tested for equality against the
  even half.

  Global schema `{E}` (binary), the edges of a digraph. The
  global program computes the paths of odd length and the
  paths of even length in mutual recursion, with `Te` as
  its output:
    `To(x, y) :- E(x, y)`
    `To(x, y) :- E(x, z), Te(z, y)`
    `Te(x, y) :- E(x, z), To(z, y)`

  Local schema `{V}` (ternary), a view that records a
  length-two path together with its midpoint. The proposed
  reformulation chains that view:
    `T↑(x, y) :- V(x, w, y)`
    `T↑(x, z) :- V(x, w, y), T↑(y, z)`

  The command is the two compiled programs run one after
  the other, and `To_aux`, `Te_aux` and `TUp_aux` are the
  snapshots the compiler generates. The single loop the
  tool verifies is computed from this sequence by the
  generic preprocessor.

  The precondition is the view constraint `V = E ∘ E` with
  the midpoint kept. The postcondition is the claim
  `T↑ = Te`.

  Expected verdict: valid. `Te` is the set of paths of even
  length at least two, which is exactly what `T↑` collects
  from the length-two view.
-/

namespace Whiel
namespace Benchmark
namespace Example4004

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, To, Te, TUp, To_aux, Te_aux, TUp_aux}
      (arity: 2),
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
      To_aux := ∅[2];
      Te_aux := ∅[2];
      To :=
        (E ∪ (π[0, 3] (σ[#1 = #2] (E × Te_aux))));
      Te := (π[0, 3] (σ[#1 = #2] (E × To_aux)));
      WHILE (¬ ((To = To_aux) ∧ (Te = Te_aux))) DO
        To_aux := To;
        Te_aux := Te;
        To :=
          (To ∪
            (E ∪
              (π[0, 3] (σ[#1 = #2] (E × Te_aux)))));
        Te :=
          (Te ∪
            (π[0, 3] (σ[#1 = #2] (E × To_aux))))
      END;
      TUp_aux := ∅[2];
      TUp :=
        ((π[0, 2] V) ∪
          (π[0, 4] (σ[#2 = #3] (V × TUp_aux))));
      WHILE (¬ (TUp = TUp_aux)) DO
        TUp_aux := TUp;
        TUp :=
          (TUp ∪
            ((π[0, 2] V) ∪
              (π[0, 4]
                (σ[#2 = #3] (V × TUp_aux)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (TUp = Te)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example4004
end Benchmark
end Whiel
