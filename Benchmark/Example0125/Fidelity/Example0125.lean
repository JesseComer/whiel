-- Author: Jesse Comer
import Obstructed.Example0125.Input
import Benchmark.Example0125.Input
import Benchmark.Fidelity.Support

/-
  Fidelity of `Benchmark/Example0125/Input.lean` to the retired
  corpus case Example0125:
  the corpus command, precondition, and postcondition are
  the retired ones under the name map `ofIndexAlphaName`
  (base names to program symbols, `X_2` snapshots to
  `X_aux`), checked by the kernel against both live
  declarations.
-/

------------------------------------------------------------
-- Fidelity Statements
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace BenchmarkFidelity
namespace Example0125

open Whiel.Concrete
open Whiel.Obstructed.Example0125
  (inputCmd inputPre inputPost)
open Whiel.Benchmark.Example0125 renaming
  inputSchema → newInputSchema,
  inputPre → newInputPre,
  inputCmd → newInputCmd,
  inputPost → newInputPost

theorem compiledCmd_eq :
    mapCmdOfIndexAlpha ofIndexAlphaName
        inputCmd.toRaw =
      newInputCmd.toRaw := by
  decide +kernel

theorem inputCmd_eq :
    (mapCmdOfIndexAlpha ofIndexAlphaName
        inputCmd.toRaw).toCmd?
        newInputSchema =
      some newInputCmd :=
  toCmd?_eq compiledCmd_eq

theorem inputPre_eq :
    mapGuardOfIndexAlpha ofIndexAlphaName
        inputPre.formula.toRaw =
      newInputPre.formula.toRaw := by
  decide

theorem inputPost_eq :
    mapGuardOfIndexAlpha ofIndexAlphaName
        inputPost.formula.toRaw =
      newInputPost.formula.toRaw := by
  decide

end Example0125
end BenchmarkFidelity
end Tests
end Synthesis
end Whiel
