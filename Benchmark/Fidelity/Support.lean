-- Author: Jesse Comer
import Whiel.Cmd.Syntax
import Whiel.Concrete.Data
import Whiel.Concrete.WhielNames

/-
  Shared support for the benchmark fidelity tests.

  A verification-task `Benchmark/ExampleNNNN/Input.lean` is
  the compiled source Datalog programs written one after
  another, under `Datalog.WhielCompiler.Naive`. Two
  mismatches stand between a compiled command and a
  canonical input file, and this module resolves both.

  Key definitions include:
    * `Whiel.Synthesis.Tests.BenchmarkFidelity.toRawInput`
    * `Whiel.Synthesis.Tests.BenchmarkFidelity.mapCmd`
    * `Whiel.Synthesis.Tests.BenchmarkFidelity.seqAfter`

  The fidelity statements are closed by:
    * `Whiel.Synthesis.Tests.BenchmarkFidelity.toCmd?_eq`

  The compiler names snapshots by incrementing a program
  symbol's index, but `Hoare.preprocess` requires every raw
  input symbol to sit at index zero, so `toRawInput` sends
  a positive-index program symbol to the auxiliary symbol
  with the same base.

  This module carries no printer of its own. A relation
  name has one surface spelling, `ProgramNames.spell`, and
  the library printers of `Whiel/Cmd/PrettyPrint.lean` and
  `Databases/UnnamedRA/PrettyPrint.lean` render through it, so
  a rendered program is one `programCmd!` reads back; that
  round trip is stated for the whole corpus in
  `Whiel/Synthesis/Tests/BenchmarkNotationRoundTrip.lean`.
-/

------------------------------------------------------------
-- Snapshot Renaming
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

open Whiel.Concrete

/-
  The canonical input name of one compiled relation name.
  Compiler snapshots are program symbols at a positive
  index, which no raw input schema may carry; each becomes
  the auxiliary symbol with the same base, one index lower.
-/
def toRawInput : ProgramNames → ProgramNames
| .programSymbol base 0 => .programSymbol base 0
| .programSymbol base (index + 1) =>
    .auxiliarySymbol base index
| name => name

/- Rename the relation names of a raw expression. -/
def mapRA
    (f : ProgramNames → ProgramNames) :
    RawRAExpr ProgramNames Data →
      RawRAExpr ProgramNames Data
| .top => .top
| .empty n => .empty n
| .rel X => .rel (f X)
| .single d => .single d
| .select φ e => .select φ (mapRA f e)
| .proj idxs e => .proj idxs (mapRA f e)
| .prod e₁ e₂ => .prod (mapRA f e₁) (mapRA f e₂)
| .union e₁ e₂ => .union (mapRA f e₁) (mapRA f e₂)
| .diff e₁ e₂ => .diff (mapRA f e₁) (mapRA f e₂)

/- Rename the relation names of a raw guard. -/
def mapGuard
    (f : ProgramNames → ProgramNames) :
    RawGuard ProgramNames Data →
      RawGuard ProgramNames Data
| .«true» => .«true»
| .«false» => .«false»
| .eq e₁ e₂ => .eq (mapRA f e₁) (mapRA f e₂)
| .subset e₁ e₂ =>
    .subset (mapRA f e₁) (mapRA f e₂)
| .eqEmptyRight e => .eqEmptyRight (mapRA f e)
| .eqEmptyLeft e => .eqEmptyLeft (mapRA f e)
| .subsetEmptyRight e =>
    .subsetEmptyRight (mapRA f e)
| .subsetEmptyLeft e => .subsetEmptyLeft (mapRA f e)
| .and φ ψ => .and (mapGuard f φ) (mapGuard f ψ)
| .or φ ψ => .or (mapGuard f φ) (mapGuard f ψ)
| .not φ => .not (mapGuard f φ)

/- Rename the relation names of a raw command. -/
def mapCmd
    (f : ProgramNames → ProgramNames) :
    RawCmd ProgramNames Data → RawCmd ProgramNames Data
| .skip => .skip
| .assign X e => .assign (f X) (mapRA f e)
| .assignEmpty X => .assignEmpty (f X)
| .seq C₁ C₂ => .seq (mapCmd f C₁) (mapCmd f C₂)
| .ite G C₁ C₂ =>
    .ite (mapGuard f G) (mapCmd f C₁) (mapCmd f C₂)
| .«while» G C =>
    .«while» (mapGuard f G) (mapCmd f C)

/-
  Write one raw command after another as a single statement
  list. Sequencing is right-nested, in the compiler's own
  `seqList` and in the concrete notation alike, so running
  `C` and then `D` is `C`'s statements followed by `D`
  rather than the pair `.seq C D`; the two denote the same
  program, but only this one is the syntax an input file
  carries.
-/
def seqAfter :
    RawCmd ProgramNames Data →
      RawCmd ProgramNames Data →
      RawCmd ProgramNames Data
| .seq C₁ C₂, E => .seq C₁ (seqAfter C₂ E)
| C, E => .seq C E

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Fidelity Statements
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

open Whiel.Concrete

/-
  A renamed compiled command that reproduces an input
  file's raw syntax checks back into that input file's
  typed command.
-/
theorem toCmd?_eq
    {Γ : UnnamedSchema ProgramNames}
    {raw : RawCmd ProgramNames Data}
    {C : Cmd Data Γ}
    (hRaw : raw = C.toRaw) :
    raw.toCmd? Γ = some C := by
  rw [hRaw]
  exact Cmd.toRaw_toCmd? C

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel

------------------------------------------------------------
-- Legacy `IndexAlphaName` Renaming
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Tests

namespace BenchmarkFidelity

open Whiel.Concrete

/-
  The `ProgramNames` symbol for one legacy `whielSch!`
  (`IndexAlphaName`) symbol. A base name (internal index
  `0`) becomes the program symbol at index `0`; an indexed
  snapshot name `X_n` for `n ≥ 2` (internal index `n - 1`)
  becomes the auxiliary symbol with the same base at index
  `n - 2`, so `T_2` becomes `T_aux` and, were a second
  snapshot of the same base ever needed, `T_3` would become
  `T_aux_1`. `Hoare.preprocess` accepts no schema symbol,
  ordinary or auxiliary, at a positive raw index, so this
  second-snapshot case cannot itself appear in a
  `Hoare.preprocess` input; every Obstructed example carries
  at most one snapshot per base.
-/
def ofIndexAlphaName : IndexAlphaName → ProgramNames
| ⟨base, 0⟩ => .programSymbol base 0
| ⟨base, index + 1⟩ => .auxiliarySymbol base index

/- Rename the relation names of a legacy raw expression. -/
def mapRAOfIndexAlpha
    (f : IndexAlphaName → ProgramNames) :
    RawRAExpr IndexAlphaName Data →
      RawRAExpr ProgramNames Data
| .top => .top
| .empty n => .empty n
| .rel X => .rel (f X)
| .single d => .single d
| .select φ e => .select φ (mapRAOfIndexAlpha f e)
| .proj idxs e => .proj idxs (mapRAOfIndexAlpha f e)
| .prod e₁ e₂ =>
    .prod (mapRAOfIndexAlpha f e₁)
      (mapRAOfIndexAlpha f e₂)
| .union e₁ e₂ =>
    .union (mapRAOfIndexAlpha f e₁)
      (mapRAOfIndexAlpha f e₂)
| .diff e₁ e₂ =>
    .diff (mapRAOfIndexAlpha f e₁)
      (mapRAOfIndexAlpha f e₂)

/- Rename the relation names of a legacy raw guard. -/
def mapGuardOfIndexAlpha
    (f : IndexAlphaName → ProgramNames) :
    RawGuard IndexAlphaName Data →
      RawGuard ProgramNames Data
| .«true» => .«true»
| .«false» => .«false»
| .eq e₁ e₂ =>
    .eq (mapRAOfIndexAlpha f e₁)
      (mapRAOfIndexAlpha f e₂)
| .subset e₁ e₂ =>
    .subset (mapRAOfIndexAlpha f e₁)
      (mapRAOfIndexAlpha f e₂)
| .eqEmptyRight e =>
    .eqEmptyRight (mapRAOfIndexAlpha f e)
| .eqEmptyLeft e =>
    .eqEmptyLeft (mapRAOfIndexAlpha f e)
| .subsetEmptyRight e =>
    .subsetEmptyRight (mapRAOfIndexAlpha f e)
| .subsetEmptyLeft e =>
    .subsetEmptyLeft (mapRAOfIndexAlpha f e)
| .and φ ψ =>
    .and (mapGuardOfIndexAlpha f φ)
      (mapGuardOfIndexAlpha f ψ)
| .or φ ψ =>
    .or (mapGuardOfIndexAlpha f φ)
      (mapGuardOfIndexAlpha f ψ)
| .not φ => .not (mapGuardOfIndexAlpha f φ)

/- Rename the relation names of a legacy raw command. -/
def mapCmdOfIndexAlpha
    (f : IndexAlphaName → ProgramNames) :
    RawCmd IndexAlphaName Data →
      RawCmd ProgramNames Data
| .skip => .skip
| .assign X e =>
    .assign (f X) (mapRAOfIndexAlpha f e)
| .assignEmpty X => .assignEmpty (f X)
| .seq C₁ C₂ =>
    .seq (mapCmdOfIndexAlpha f C₁)
      (mapCmdOfIndexAlpha f C₂)
| .ite G C₁ C₂ =>
    .ite (mapGuardOfIndexAlpha f G)
      (mapCmdOfIndexAlpha f C₁)
      (mapCmdOfIndexAlpha f C₂)
| .«while» G C =>
    .«while» (mapGuardOfIndexAlpha f G)
      (mapCmdOfIndexAlpha f C)

end BenchmarkFidelity

end Tests

end Synthesis

end Whiel
