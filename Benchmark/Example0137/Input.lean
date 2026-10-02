-- Benchmark contributors: Fangzhu Shen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Transitive closure computed non-linearly, against all
  paths computed through linear odd and even halves.

  Schema `{E, TX, TaY, TbY, TcY}` (all binary). `E` is the
  edge relation of a digraph, `TX` the non-linear closure,
  and the `Y` relations the odd/even program's, with `TcY`
  the union of the two halves. `TX_aux`, `TaY_aux`,
  `TbY_aux` and `TcY_aux` are the snapshots the compiler
  generates.

  The first program is
    `TX(x, y) :- E(x, y)`
    `TX(x, y) :- TX(x, z), TX(z, y)`
  and the second is
    `TbY(x, y) :- E(x, y)`
    `TbY(x, y) :- E(x, z), TaY(z, y)`
    `TaY(x, y) :- E(x, z), TbY(z, y)`
    `TcY(x, y) :- TaY(x, y)`
    `TcY(x, y) :- TbY(x, y)`

  The command is the two compiled programs run one after
  the other. The single loop the tool verifies is computed
  from that sequence by the generic preprocessor.

  The precondition is `true`. The postcondition is that
  the two computations agree, `TX = TcY`. Each output
  relation starts empty and accumulates its program's
  immediate consequences, and each loop exits only when
  every output equals its snapshot, so on exit `TX` and
  `TcY` hold the least fixpoints of the two programs; the
  postcondition compares those fixpoints.

  Expected verdict: valid. Every path has odd or even
  length, so the union of the two halves is the transitive
  closure.
-/

namespace Whiel
namespace Benchmark
namespace Example0137

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, TX, TaY, TbY, TcY,
      TX_aux, TaY_aux, TbY_aux, TcY_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TX_aux := ∅[2];
      TX :=
        (E ∪
          (π[0, 3] (σ[#1 = #2] (TX_aux × TX_aux))));
      WHILE (¬ (TX = TX_aux)) DO
        TX_aux := TX;
        TX :=
          (TX ∪
            (E ∪
              (π[0, 3]
                (σ[#1 = #2] (TX_aux × TX_aux)))))
      END;
      TbY_aux := ∅[2];
      TaY_aux := ∅[2];
      TcY_aux := ∅[2];
      TbY :=
        (E ∪ (π[0, 3] (σ[#1 = #2] (E × TaY_aux))));
      TaY := (π[0, 3] (σ[#1 = #2] (E × TbY_aux)));
      TcY := (TaY_aux ∪ TbY_aux);
      WHILE
          (¬ ((TbY = TbY_aux) ∧
            ((TaY = TaY_aux) ∧ (TcY = TcY_aux)))) DO
        TbY_aux := TbY;
        TaY_aux := TaY;
        TcY_aux := TcY;
        TbY :=
          (TbY ∪
            (E ∪
              (π[0, 3]
                (σ[#1 = #2] (E × TaY_aux)))));
        TaY :=
          (TaY ∪
            (π[0, 3] (σ[#1 = #2] (E × TbY_aux))));
        TcY := (TcY ∪ (TaY_aux ∪ TbY_aux))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (TX = TcY)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0137
end Benchmark
end Whiel
