-- Author: Jesse Comer
import Benchmark.Example2004.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example2004/Input.lean` to its
  source Datalog programs.

  The two Datalog programs below are the magic-set
  transformation — one program whose two output relations
  are the demand set `MPath` and the restricted answers
  `PathBF` — and the right-linear path program it was
  derived from.

  Compiling each program with the naive compiler and
  writing the results one after the other, with the
  generated snapshots renamed to auxiliary input names,
  reproduces the input file's command exactly, so the
  encoding is faithful by construction rather than by
  inspection. The single loop the tool verifies is
  computed from that sequence by the generic
  preprocessor and is pinned at the end of this module.

  Two things about the reference encoding of this problem.
  First, it ran the two programs in one hand-written loop
  that iterated destructively: it assigned
  `MPath_aux := MPath` and then recomputed `MPath` from
  `MPath_aux` alone, so the relations stepped the
  immediate-consequence operator `T ↦ T_P(T)`. It did not
  start from the empty relation: it initialised
  `MPath := { "root" }`, `PathBF := ∅` and
  `Path := Edge`, which is `T_P(∅)`, one step along the
  same chain. That operator is monotone, so its orbit
  from `∅` is increasing and its limit is the least
  fixpoint, and dropping the first term of an increasing
  chain does not move the limit — so the reference loop
  and the compiled accumulating form
  `T := T ∪ T_P(T)` reach the same least fixpoint, and
  the reference postcondition
  `(π[1, 2] (σ[#0 = #1] (MPath × Path)) ⊆ PathBF) ∧
  (PathBF ⊆ Path)` is the input file's postcondition
  unchanged, read over those fixpoints.

  Second, the reference command seeded the demand set with
  the constant relation `{ "root" }` written inside the
  assignment to `MPath`. A Datalog rule head carries no
  constants, so the seed is a source relation `Root` here,
  read by the rule `MPath(x) :- Root(x)` and pinned to
  `{ "root" }` by the precondition; the two encodings fix
  the same demand set.
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

namespace Example2004

open Whiel.Concrete

def Edge : ProgramNames :=
  .programSymbol ⟨"Edge", by decide⟩ 0

def Root : ProgramNames :=
  .programSymbol ⟨"Root", by decide⟩ 0

def MPath : ProgramNames :=
  .programSymbol ⟨"MPath", by decide⟩ 0

def PathBF : ProgramNames :=
  .programSymbol ⟨"PathBF", by decide⟩ 0

def Path : ProgramNames :=
  .programSymbol ⟨"Path", by decide⟩ 0

/- The transformed program's schema. -/
def schemaM : UnnamedSchema ProgramNames :=
  programSch![
    {Root, MPath} (arity: 1),
    {Edge, PathBF} (arity: 2)
  ]

/- The original program's schema. -/
def schemaP : UnnamedSchema ProgramNames :=
  programSch![
    {Edge, Path} (arity: 2)
  ]

/- The magic-set transformation: demand and answers. -/
def programM : Datalog.Program Data schemaM :=
  datalog![
    MPath(x1) :- Root(x1);
    MPath(y1) :- MPath(x1), Edge(x1, y1);
    PathBF(x1, y1) :- MPath(x1), Edge(x1, y1);
    PathBF(x1, x2) :-
      MPath(x1), Edge(x1, y1), PathBF(y1, x2);
  ]

/- The original right-linear path program. -/
def programP : Datalog.Program Data schemaP :=
  datalog![
    Path(x1, y1) :- Edge(x1, y1);
    Path(x1, x2) :- Edge(x1, y1), Path(y1, x2);
  ]

end Example2004

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

namespace Example2004

open Whiel.Concrete

/- The compiled transformed program, in input names. -/
def rawM : RawCmd ProgramNames Data :=
  mapCmd toRawInput programM.toWhielCmd.toRaw

/- The compiled original program, in input names. -/
def rawP : RawCmd ProgramNames Data :=
  mapCmd toRawInput programP.toWhielCmd.toRaw

/- The reduction: the two compiled programs in sequence. -/
def compiledRaw : RawCmd ProgramNames Data :=
  seqAfter rawM rawP

end Example2004

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

namespace Example2004

open Whiel.Concrete

open Whiel.Benchmark.Example2004
  (inputSchema inputPre inputCmd inputPost)

/- The seed: the query is asked at `"root"`. -/
def seedRaw : RawGuard ProgramNames Data :=
  .eq (.rel Root) (.single (Data.str "root"))

/- The claim: completeness on demand, then soundness. -/
def claimRaw : RawGuard ProgramNames Data :=
  .and
    (.subset
      (.proj [1, 2]
        (.select (Sel.eqIdx 0 1)
          (.prod (.rel MPath) (.rel Path))))
      (.rel PathBF))
    (.subset (.rel PathBF) (.rel Path))

theorem inputPre_eq :
    inputPre.formula.toRaw = seedRaw := by
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

end Example2004

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

namespace Example2004

open Whiel.Benchmark.Example2004 (inputPreproc)

/-
  The single loop the generic preprocessor computes
  from the sequence above. It is what the tool verifies,
  so it is pinned here rather than only displayed.
-/
/-- info:
WHILE ((¬(((MPath = MPath_aux) ∧ (PathBF = PathBF_aux)))) ∨ (¬((Path = Path_aux)))) DO
IF (¬(((MPath = MPath_aux) ∧ (PathBF = PathBF_aux)))) THEN
MPath_aux := MPath;
PathBF_aux := PathBF;
MPath := (MPath ∪ (Root ∪ π[2] (σ[#0 = #1] ((MPath_aux × Edge)))));
PathBF := (PathBF ∪ (π[0,2] (σ[#0 = #1] ((MPath_aux × Edge))) ∪ π[0,4] (σ[(#0 = #1 ∧ #2 = #3)] ((MPath_aux × (Edge × PathBF_aux))))))
ELSE
SKIP
END;
IF (¬((Path = Path_aux))) THEN
Path_aux := Path;
Path := (Path ∪ (Edge ∪ π[0,3] (σ[#1 = #2] ((Edge × Path_aux)))))
ELSE
SKIP
END
END
-/
#guard_msgs (whitespace := lax) in
#eval DBTPretty.display ("\n" ++ inputPreproc.loopCmd.pretty)

end Example2004

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
