-- Author: Jesse Comer
import Benchmark.Example4035.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example4035/Input.lean` to its
  source Datalog programs.

  The two Datalog programs below are the good-interior walk
  query and its reformulation over the two conjunctive
  views.

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

namespace Example4035

open Whiel.Concrete

def E : ProgramNames :=
  .programSymbol ⟨"E", by decide⟩ 0

def G : ProgramNames :=
  .programSymbol ⟨"G", by decide⟩ 0

def T : ProgramNames :=
  .programSymbol ⟨"T", by decide⟩ 0

def Vb : ProgramNames :=
  .programSymbol ⟨"Vb", by decide⟩ 0

def Ve : ProgramNames :=
  .programSymbol ⟨"Ve", by decide⟩ 0

def TUp : ProgramNames :=
  .programSymbol ⟨"TUp", by decide⟩ 0

/- The global schema and its good-interior path query. -/
def globalSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, T} (arity: 2),
    {G} (arity: 1)
  ]

/- The local schema and the reformulation's output. -/
def localSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Vb, Ve, TUp} (arity: 2)
  ]

/- `T xy :- Exz, Gz, Ezy` and `T xy :- Exz, Gz, T zy`. -/
def globalProgram : Datalog.Program Data globalSchema :=
  datalog![
    T(x1, y1) :- E(x1, z1), G(z1), E(z1, y1);
    T(x1, y1) :- E(x1, z1), G(z1), T(z1, y1);
  ]

/- `T↑ xy :- Ve xz, Vb zy` and `T↑ xy :- Ve xz, T↑ zy`. -/
def localProgram : Datalog.Program Data localSchema :=
  datalog![
    TUp(x1, y1) :- Ve(x1, z1), Vb(z1, y1);
    TUp(x1, y1) :- Ve(x1, z1), TUp(z1, y1);
  ]

end Example4035

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

namespace Example4035

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

end Example4035

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

namespace Example4035

open Whiel.Concrete

open Whiel.Benchmark.Example4035
  (inputSchema inputPre inputCmd inputPost)

/- `Vb = G ⋈ E`, the edges out of a good vertex. -/
def beginGoodRaw : RawRAExpr ProgramNames Data :=
  .proj [1, 2]
    (.select (Sel.eqIdx 0 1)
      (.prod (.rel G) (.rel E)))

/- `Ve = E ⋈ G`, the edges into a good vertex. -/
def endGoodRaw : RawRAExpr ProgramNames Data :=
  .proj [0, 1]
    (.select (Sel.eqIdx 1 2)
      (.prod (.rel E) (.rel G)))

/- The two exact conjunctive view equations. -/
def viewConstraintRaw : RawGuard ProgramNames Data :=
  .and (.eq (.rel Vb) beginGoodRaw)
    (.eq (.rel Ve) endGoodRaw)

/- The claim `T = T↑`. -/
def claimRaw : RawGuard ProgramNames Data :=
  .eq (.rel T) (.rel TUp)

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

end Example4035

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

namespace Example4035

open Whiel.Benchmark.Example4035 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬((T = T_aux))) ∨ (¬((TUp = TUp_aux)))) DO
IF (¬((T = T_aux))) THEN
T_aux := T;
T := (T ∪ (π[0,4] (σ[(#1 = #2 ∧ #1 = #3)] ((E × (G × E)))) ∪ π[0,4] (σ[(#1 = #2 ∧ #1 = #3)] ((E × (G × T_aux))))))
ELSE
SKIP
END;
IF (¬((TUp = TUp_aux))) THEN
TUp_aux := TUp;
TUp := (TUp ∪ (π[0,3] (σ[#1 = #2] ((Ve × Vb))) ∪ π[0,3] (σ[#1 = #2] ((Ve × TUp_aux)))))
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example4035

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
