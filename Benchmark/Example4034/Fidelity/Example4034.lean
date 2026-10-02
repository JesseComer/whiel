-- Author: Jesse Comer
import Benchmark.Example4034.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example4034/Input.lean` to its
  source Datalog programs.

  The three Datalog programs below are the reformulation
  over the two source views, the odd/even program those
  views are sound for, and the global transitive closure.

  Compiling each program with the naive compiler and
  writing the results one after the other, with the
  generated snapshots renamed to auxiliary input names,
  reproduces the input file's command exactly, so the
  encoding is faithful by construction rather than by
  inspection. The single loop the tool verifies is
  computed from that sequence by the generic
  preprocessor and is pinned at the end of this module.
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

namespace Example4034

open Whiel.Concrete

def E : ProgramNames :=
  .programSymbol ⟨"E", by decide⟩ 0

def T : ProgramNames :=
  .programSymbol ⟨"T", by decide⟩ 0

def To : ProgramNames :=
  .programSymbol ⟨"To", by decide⟩ 0

def Te : ProgramNames :=
  .programSymbol ⟨"Te", by decide⟩ 0

def Vo : ProgramNames :=
  .programSymbol ⟨"Vo", by decide⟩ 0

def Ve : ProgramNames :=
  .programSymbol ⟨"Ve", by decide⟩ 0

def TUp : ProgramNames :=
  .programSymbol ⟨"TUp", by decide⟩ 0

/- The local schema: two sources and the output. -/
def localSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Vo, Ve, TUp} (arity: 2)
  ]

/- The global schema and the odd/even view relations. -/
def viewSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, To, Te} (arity: 2)
  ]

/- The global schema and its transitive-closure output. -/
def globalSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, T} (arity: 2)
  ]

/- `T↑ xy :- Vo xy` and `T↑ xy :- Ve xy`. -/
def localProgram : Datalog.Program Data localSchema :=
  datalog![
    TUp(x1, y1) :- Vo(x1, y1);
    TUp(x1, y1) :- Ve(x1, y1);
  ]

/- The odd/even program defining the two views. -/
def viewProgram : Datalog.Program Data viewSchema :=
  datalog![
    To(x1, y1) :- E(x1, y1);
    To(x1, y1) :- E(x1, z1), Te(z1, y1);
    Te(x1, y1) :- E(x1, z1), To(z1, y1);
  ]

/- `T xy :- Exy` and `T xy :- Exz, T zy`. -/
def globalProgram : Datalog.Program Data globalSchema :=
  datalog![
    T(x1, y1) :- E(x1, y1);
    T(x1, y1) :- E(x1, z1), T(z1, y1);
  ]

end Example4034

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

namespace Example4034

open Whiel.Concrete

/- The compiled reformulation, in input names. -/
def localRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput localProgram.toWhielCmd.toRaw

/- The compiled view program, in input names. -/
def viewRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput viewProgram.toWhielCmd.toRaw

/- The compiled global program, in input names. -/
def globalRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput globalProgram.toWhielCmd.toRaw

/- The reduction: the three compiled programs in sequence. -/
def compiledRaw : RawCmd ProgramNames Data :=
  seqAfter localRaw (seqAfter viewRaw globalRaw)

end Example4034

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

namespace Example4034

open Whiel.Concrete

open Whiel.Benchmark.Example4034
  (inputSchema inputPre inputCmd inputPost)

/- The sources are unconstrained on entry. -/
def noConstraintRaw : RawGuard ProgramNames Data :=
  .«true»

/- The claim `(Vo ⊆ To ∧ Ve ⊆ Te) → T↑ ⊆ T`. -/
def claimRaw : RawGuard ProgramNames Data :=
  .or
    (.not
      (.and (.subset (.rel Vo) (.rel To))
        (.subset (.rel Ve) (.rel Te))))
    (.subset (.rel TUp) (.rel T))

theorem inputPre_eq :
    inputPre.formula.toRaw = noConstraintRaw := by
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

end Example4034

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

namespace Example4034

open Whiel.Benchmark.Example4034 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬((TUp = TUp_aux))) ∨ ((¬(((To = To_aux) ∧ (Te = Te_aux)))) ∨ (¬((T = T_aux))))) DO
IF (¬((TUp = TUp_aux))) THEN
TUp_aux := TUp;
TUp := (TUp ∪ (Vo ∪ Ve))
ELSE
SKIP
END;
IF ((¬(((To = To_aux) ∧ (Te = Te_aux)))) ∨ (¬((T = T_aux)))) THEN
IF (¬(((To = To_aux) ∧ (Te = Te_aux)))) THEN
To_aux := To;
Te_aux := Te;
To := (To ∪ (E ∪ π[0,3] (σ[#1 = #2] ((E × Te_aux)))));
Te := (Te ∪ π[0,3] (σ[#1 = #2] ((E × To_aux))))
ELSE
SKIP
END;
IF (¬((T = T_aux))) THEN
T_aux := T;
T := (T ∪ (E ∪ π[0,3] (σ[#1 = #2] ((E × T_aux)))))
ELSE
SKIP
END
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example4034

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
