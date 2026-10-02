-- Author: Jesse Comer
import Benchmark.Example4001.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example4001/Input.lean` to its
  source Datalog programs.

  The two Datalog programs below are the triangle query and
  its length-two path-view reformulation. Neither is
  recursive; the compiler is applied all the same, so each
  carries the one WHILE loop it emits.

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

namespace Example4001

open Whiel.Concrete

def E : ProgramNames :=
  .programSymbol ⟨"E", by decide⟩ 0

def Q : ProgramNames :=
  .programSymbol ⟨"Q", by decide⟩ 0

def V : ProgramNames :=
  .programSymbol ⟨"V", by decide⟩ 0

def QUp : ProgramNames :=
  .programSymbol ⟨"QUp", by decide⟩ 0

/- The global schema and its triangle-query output. -/
def globalSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Q} (arity: 1),
    {E} (arity: 2)
  ]

/- The local schema and the reformulation's output. -/
def localSchema : UnnamedSchema ProgramNames :=
  programSch![
    {QUp} (arity: 1),
    {V} (arity: 3)
  ]

/- `Q x :- Exy, Eyz, Ezx`. -/
def globalProgram : Datalog.Program Data globalSchema :=
  datalog![
    Q(x1) :- E(x1, y1), E(y1, z1), E(z1, x1);
  ]

/- `Q↑ x :- V xyz, V yzx`. -/
def localProgram : Datalog.Program Data localSchema :=
  datalog![
    QUp(x1) :- V(x1, y1, z1), V(y1, z1, x1);
  ]

end Example4001

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

namespace Example4001

open Whiel.Concrete

/- The compiled global program, in input names. -/
def globalRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput globalProgram.toWhielCmd.toRaw

/- The compiled local program, in input names. -/
def localRaw : RawCmd ProgramNames Data :=
  mapCmd toRawInput localProgram.toWhielCmd.toRaw

/- The reduction: the two compiled programs in sequence. -/
def compiledRaw : RawCmd ProgramNames Data :=
  seqAfter globalRaw localRaw

end Example4001

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

namespace Example4001

open Whiel.Concrete

open Whiel.Benchmark.Example4001
  (inputSchema inputPre inputCmd inputPost)

/- `V = E ∘ E`, keeping the midpoint. -/
def viewConstraintRaw : RawGuard ProgramNames Data :=
  .eq (.rel V)
    (.proj [0, 1, 3]
      (.select (Sel.eqIdx 1 2)
        (.prod (.rel E) (.rel E))))

/- The claim `Q = Q↑`. -/
def claimRaw : RawGuard ProgramNames Data :=
  .eq (.rel Q) (.rel QUp)

theorem inputPre_eq :
    inputPre.formula.toRaw = viewConstraintRaw := by
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

end Example4001

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

namespace Example4001

open Whiel.Benchmark.Example4001 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬((Q = Q_aux))) ∨ (¬((QUp = QUp_aux)))) DO
IF (¬((Q = Q_aux))) THEN
Q_aux := Q;
Q := (Q ∪ π[0] (σ[((#1 = #2 ∧ #3 = #4) ∧ #0 = #5)] ((E × (E × E)))))
ELSE
SKIP
END;
IF (¬((QUp = QUp_aux))) THEN
QUp_aux := QUp;
QUp := (QUp ∪ π[0] (σ[((#1 = #3 ∧ #2 = #4) ∧ #0 = #5)] ((V × V))))
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example4001

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
