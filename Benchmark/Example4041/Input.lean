-- Benchmark contributors: Jesse Comer, Val Tannen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Transitive closure and a reformulation read off two
  exact odd/even views.

  Global schema `{E}` (binary), the edges of a digraph, with
  the standard right-linear transitive closure:
    `T(x, y) :- E(x, y)`
    `T(x, y) :- E(x, z), T(z, y)`

  The local schema is `{To, Te}`, and the views are exact,
  so they are not free source tables: they are computed
  from `E` by the odd/even path program
    `To(x, y) :- E(x, y)`
    `To(x, y) :- E(x, z), Te(z, y)`
    `Te(x, y) :- E(x, z), To(z, y)`
  and the reformulation is a program over that local
  schema:
    `T↑(x, y) :- To(x, y)`
    `T↑(x, y) :- Te(x, y)`

  The command is the three compiled programs run one after
  the other — the closure, the views, then the
  reformulation, which reads the views the program before
  it computed — and `T_aux`, `To_aux`, `Te_aux` and
  `TUp_aux` are the snapshots the compiler generates. The
  single loop the tool verifies is computed from this
  sequence by the generic preprocessor.

  The exactness of the views is carried by the computation
  itself, so the precondition is `true`; the postcondition
  is the claim `T↑ = T`.

  Expected verdict: valid. `To` collects the paths of odd
  length and `Te` the paths of even length at least two, so
  their union is exactly the transitive closure.
-/

namespace Whiel
namespace Benchmark
namespace Example4041

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, T, To, Te, TUp, T_aux, To_aux, Te_aux,
      TUp_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T_aux := ∅[2];
      T :=
        (E ∪ (π[0, 3] (σ[#1 = #2] (E × T_aux))));
      WHILE (¬ (T = T_aux)) DO
        T_aux := T;
        T :=
          (T ∪
            (E ∪
              (π[0, 3] (σ[#1 = #2] (E × T_aux)))))
      END;
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
      TUp := (To ∪ Te);
      WHILE (¬ (TUp = TUp_aux)) DO
        TUp_aux := TUp;
        TUp := (TUp ∪ (To ∪ Te))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (TUp = T)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example4041
end Benchmark
end Whiel
