-- Author: Jesse Comer
import Benchmark.Example0137.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example0137/Input.lean` to its
  source Datalog programs.

  The two Datalog programs below are the non-linear
  transitive closure and the linear odd/even path program
  with the union of its two halves.

  Compiling each program with the naive compiler and
  writing the results one after the other, with the
  generated snapshots renamed to auxiliary input names,
  reproduces the input file's command exactly, so the
  encoding is faithful by construction rather than by
  inspection. The single loop the tool verifies is
  computed from that sequence by the generic
  preprocessor and is pinned at the end of this module.

  The reference encoding of this problem ran the two
  programs in one hand-written loop that iterated
  destructively: it carried a second copy `SX` of each
  relation, assigned `TX := SX` and then recomputed `SX`
  from the new `TX`, so the pair stepped the
  immediate-consequence operator `T ↦ T_P(T)` from the
  empty relation. That operator is monotone, so its orbit
  from `∅` is increasing and its limit is the least
  fixpoint — the same limit the compiled accumulating
  form `T := T ∪ T_P(T)` reaches. The reference
  postcondition was `TX = TcY` over those previous-round
  copies, which at loop exit equal the fixpoints; the
  input file states the same equality over the compiled
  output relations, which hold the fixpoints on exit, so
  the two say the same thing.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.hashCommand false

------------------------------------------------------------
-- Datalog Sources
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example0137

open Whiel.Concrete

def E : ProgramNames :=
  .programSymbol ⟨"E", by decide⟩ 0

def TX : ProgramNames :=
  .programSymbol ⟨"TX", by decide⟩ 0

def TaY : ProgramNames :=
  .programSymbol ⟨"TaY", by decide⟩ 0

def TbY : ProgramNames :=
  .programSymbol ⟨"TbY", by decide⟩ 0

def TcY : ProgramNames :=
  .programSymbol ⟨"TcY", by decide⟩ 0

/- The closure program's schema. -/
def schemaX : UnnamedSchema ProgramNames :=
  programSch![
    {E, TX} (arity: 2)
  ]

/- The odd/even program's schema. -/
def schemaY : UnnamedSchema ProgramNames :=
  programSch![
    {E, TaY, TbY, TcY} (arity: 2)
  ]

/- Transitive closure, non-linearly. -/
def programX : Datalog.Program Data schemaX :=
  datalog![
    TX(x1, y1) :- E(x1, y1);
    TX(x1, y1) :- TX(x1, z1), TX(z1, y1);
  ]

/- Odd and even paths and their union, linearly. -/
def programY : Datalog.Program Data schemaY :=
  datalog![
    TbY(x1, y1) :- E(x1, y1);
    TbY(x1, y1) :- E(x1, z1), TaY(z1, y1);
    TaY(x1, y1) :- E(x1, z1), TbY(z1, y1);
    TcY(x1, y1) :- TaY(x1, y1);
    TcY(x1, y1) :- TbY(x1, y1);
  ]

end Example0137

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Compiled Sequence
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example0137

open Whiel.Concrete

/- The compiled closure program, in input names. -/
def rawX : RawCmd ProgramNames Data :=
  mapCmd toRawInput programX.toWhielCmd.toRaw

/- The compiled odd/even program, in input names. -/
def rawY : RawCmd ProgramNames Data :=
  mapCmd toRawInput programY.toWhielCmd.toRaw

/- The reduction: the two compiled programs in sequence. -/
def compiledRaw : RawCmd ProgramNames Data :=
  seqAfter rawX rawY

end Example0137

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Input Fidelity
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example0137

open Whiel.Concrete

open Whiel.Benchmark.Example0137
  (inputSchema inputPre inputCmd inputPost)

/- The claim: the two computations agree. -/
def claimRaw : RawGuard ProgramNames Data :=
  .eq (.rel TX) (.rel TcY)

theorem inputPre_eq :
    inputPre.formula.toRaw = .«true» := by
  decide

theorem inputPost_eq :
    inputPost.formula.toRaw = claimRaw := by
  decide

theorem compiledRaw_eq :
    compiledRaw = inputCmd.toRaw := by
  decide +kernel

/- The renamed sequence is the input file's command. -/
theorem inputCmd_eq :
    compiledRaw.toCmd? inputSchema = some inputCmd :=
  toCmd?_eq compiledRaw_eq

end Example0137

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Preprocessed Loop
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

namespace Example0137

open Whiel.Benchmark.Example0137 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬((TX = TX_aux))) ∨ (¬(((TbY = TbY_aux) ∧ ((TaY = TaY_aux) ∧ (TcY = TcY_aux)))))) DO
IF (¬((TX = TX_aux))) THEN
TX_aux := TX;
TX := (TX ∪ (E ∪ π[0,3] (σ[#1 = #2] ((TX_aux × TX_aux)))))
ELSE
SKIP
END;
IF (¬(((TbY = TbY_aux) ∧ ((TaY = TaY_aux) ∧ (TcY = TcY_aux))))) THEN
TbY_aux := TbY;
TaY_aux := TaY;
TcY_aux := TcY;
TbY := (TbY ∪ (E ∪ π[0,3] (σ[#1 = #2] ((E × TaY_aux)))));
TaY := (TaY ∪ π[0,3] (σ[#1 = #2] ((E × TbY_aux))));
TcY := (TcY ∪ (TaY_aux ∪ TbY_aux))
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example0137

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
