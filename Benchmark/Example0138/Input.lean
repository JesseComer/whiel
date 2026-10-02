-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Transitive closure and the union of odd and even paths,
  both computed non-linearly, compared.

  Schema `{E, TX, TaY, TbY, TcY}` (all binary). `E` is the
  edge relation of a digraph; `TX` is the closure program's
  output, `TaY`, `TbY`, `TcY` the odd/even program's
  outputs. `TX_aux`, `TaY_aux`, `TbY_aux` and `TcY_aux` are
  the snapshots the compiler generates.

  The closure program is the non-linear transitive closure
    `TX(x, y) :- E(x, y)`
    `TX(x, y) :- TX(x, z), TX(z, y)`
  and the odd/even program is the non-linear one with the
  union of its two halves
    `TaY(x, y) :- E(x, z), E(z, y)`
    `TaY(x, y) :- TaY(x, z), TaY(z, y)`
    `TaY(x, y) :- TbY(x, z), TbY(z, y)`
    `TbY(x, y) :- E(x, y)`
    `TbY(x, y) :- TbY(x, z), TaY(z, y)`
    `TbY(x, y) :- TaY(x, z), TbY(z, y)`
    `TcY(x, y) :- TaY(x, y)`
    `TcY(x, y) :- TbY(x, y)`

  The command is the two compiled programs run one after
  the other. The single loop the tool verifies is computed
  from that sequence by the generic preprocessor.

  The precondition is `true`. The postcondition is that the
  two computations agree, `TX = TcY`. Each output relation
  starts empty and accumulates its program's immediate
  consequences, and each loop exits only when every output
  equals its snapshot, so on exit the outputs hold the least
  fixpoints of the two programs; the postcondition compares
  those fixpoints.

  Expected verdict: valid. Both sides compute the set of
  pairs joined by a path of one or more edges: `TX` by
  squaring, `TcY` as the union of the odd-length and the
  even-length paths.

  Reference encoding: the legacy Example0138 ran the two programs in one hand-written lockstep loop
  that iterated destructively from the empty relations (the retired corpus case Example0138). Its
  immediate-consequence operator is monotone, so its orbit from the empty relations is increasing
  and reaches the same least fixpoints as the accumulating compiled loops; the reference
  postcondition `TX = TcY` over the previous-round copies says the same as the postcondition here.
-/

namespace Whiel
namespace Benchmark
namespace Example0138

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, TX, TaY, TbY, TcY, TX_aux, TaY_aux, TbY_aux, TcY_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TX_aux := ∅[2];
      TX := (E ∪ π[0,3] (σ[#1 = #2] ((TX_aux × TX_aux))));
      WHILE (¬((TX = TX_aux))) DO
        TX_aux := TX;
        TX := (TX ∪ (E ∪ π[0,3] (σ[#1 = #2] ((TX_aux × TX_aux)))))
      END;
      TaY_aux := ∅[2];
      TbY_aux := ∅[2];
      TcY_aux := ∅[2];
      TaY := (π[0,3] (σ[#1 = #2] ((E × E))) ∪ (π[0,3] (σ[#1 = #2] ((TaY_aux × TaY_aux))) ∪ π[0,3] (σ[#1 = #2] ((TbY_aux × TbY_aux)))));
      TbY := (E ∪ (π[0,3] (σ[#1 = #2] ((TbY_aux × TaY_aux))) ∪ π[0,3] (σ[#1 = #2] ((TaY_aux × TbY_aux)))));
      TcY := (TaY_aux ∪ TbY_aux);
      WHILE (¬(((TaY = TaY_aux) ∧ ((TbY = TbY_aux) ∧ (TcY = TcY_aux))))) DO
        TaY_aux := TaY;
        TbY_aux := TbY;
        TcY_aux := TcY;
        TaY := (TaY ∪ (π[0,3] (σ[#1 = #2] ((E × E))) ∪ (π[0,3] (σ[#1 = #2] ((TaY_aux × TaY_aux))) ∪ π[0,3] (σ[#1 = #2] ((TbY_aux × TbY_aux))))));
        TbY := (TbY ∪ (E ∪ (π[0,3] (σ[#1 = #2] ((TbY_aux × TaY_aux))) ∪ π[0,3] (σ[#1 = #2] ((TaY_aux × TbY_aux))))));
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

end Example0138
end Benchmark
end Whiel
