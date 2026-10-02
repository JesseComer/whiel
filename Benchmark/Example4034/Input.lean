-- Benchmark contributors: Leo Zhang, Val Tannen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Transitive closure and a reformulation read off two
  sound odd/even views.

  Global schema `{E}` (binary), the edges of a digraph, with
  the standard right-linear transitive closure:
    `T(x, y) :- E(x, y)`
    `T(x, y) :- E(x, z), T(z, y)`

  The two views the local schema stands for are defined by
  the odd/even path program over `E`:
    `To(x, y) :- E(x, y)`
    `To(x, y) :- E(x, z), Te(z, y)`
    `Te(x, y) :- E(x, z), To(z, y)`

  Local schema `{Vo, Ve}`, whose two relations are source
  tables that the views only have to be sound for, with
  the loop-free reformulation:
    `T↑(x, y) :- Vo(x, y)`
    `T↑(x, y) :- Ve(x, y)`

  The command is the three compiled programs run one after
  the other — the reformulation, the odd/even views, then
  the closure — and `TUp_aux`, `To_aux`, `Te_aux` and
  `T_aux` are the snapshots the compiler generates. `Vo`
  and `Ve` are never assigned. The single loop the tool
  verifies is computed from this sequence by the generic
  preprocessor.

  Soundness relates the source tables to the least
  fixpoints the loop computes, so it cannot be a
  precondition: the precondition is `true` and the
  postcondition states that soundness implies the claim,
    `(Vo ⊆ To ∧ Ve ⊆ Te) → T↑ ⊆ T`
  written with `¬` and `∨`.

  Expected verdict: valid. `Vo ∪ Ve ⊆ To ∪ Te = T`.
-/

namespace Whiel
namespace Benchmark
namespace Example4034

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, Vo, Ve, T, To, Te, TUp, T_aux, To_aux,
      Te_aux, TUp_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TUp_aux := ∅[2];
      TUp := (Vo ∪ Ve);
      WHILE (¬ (TUp = TUp_aux)) DO
        TUp_aux := TUp;
        TUp := (TUp ∪ (Vo ∪ Ve))
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
      T_aux := ∅[2];
      T :=
        (E ∪ (π[0, 3] (σ[#1 = #2] (E × T_aux))));
      WHILE (¬ (T = T_aux)) DO
        T_aux := T;
        T :=
          (T ∪
            (E ∪
              (π[0, 3] (σ[#1 = #2] (E × T_aux)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((¬ ((Vo ⊆ To) ∧ (Ve ⊆ Te))) ∨ (TUp ⊆ T))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example4034
end Benchmark
end Whiel
