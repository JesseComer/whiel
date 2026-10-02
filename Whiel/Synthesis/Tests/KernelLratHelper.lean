-- Author: Jesse Comer
import Mathlib.Tactic.Sat.FromLRAT

/-
  Fixture for the kernel-checked LRAT replacement of AVATAR
  refutations.

  The block below is the exact text the proof transformation
  emits in place of one pinned emitter helper: the captured
  `casc_2025` AVATAR step of an initialization obligation,
  whose Boolean helper was closed by `bv_decide` and whose
  `Prop` bridge discharged itself from it. `bv_decide` adds a
  `_native.bv_decide.ax…` axiom, so that proof cannot audit
  to std3; `lrat_proof` builds a term the kernel checks, and
  the bridge is ordinary `Or.elim` over the original clauses.

  The theorem statement is the emitted one, unchanged. Both
  audits below must report exactly std3, which is what makes
  the transformation admissible: it is outside the trust
  boundary, and this file is where that is checked on a
  fixture rather than on a generated certificate.

  Keep this block byte-identical to the transformation's own
  renderer (`whiel_runner/src/framework2/proof_transform/
  lrat.rs`, `render_lrat_helper`), whose unit tests pin the
  same text.
-/

set_option linter.style.setOption false
-- The bridge's proof term is one line because the renderer emits it as
-- one line; wrapping it here would stop this file from being the
-- byte-for-byte fixture it is meant to be.
set_option linter.style.longLine false
set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

namespace Whiel
namespace Synthesis
namespace Tests
namespace KernelLratHelper

variable (sA2 sA3 sA15 : Prop)

-- step 199 avatar sat refutation via kernel-checked LRAT
lrat_proof inf_s199_lrat
  "p cnf 3 4\n1 2 0\n3 0\n-1 -3 0\n-2 0\n"
  "5 -1 0 2 3 0\n5 d 3 0\n6 2 0 5 1 0\n7 0 6 4 0\n"

theorem inf_s199 : (sA2 ∨ sA3) → (sA15) → ((¬sA2) ∨ (¬sA15)) → ((¬sA3)) → False := by
  intro h1 h2 h3 h4
  have h := inf_s199_lrat sA2 sA3 sA15
  exact (fun hs => Or.elim hs (fun hs => Or.elim hs (fun hf => Or.elim h1 hf.1 (fun hr => hf.2 hr)) (fun hf => hf h2)) (fun hs => Or.elim hs (fun hf => Or.elim h3 (fun hn => hn hf.1) (fun hr => (fun hn => hn hf.2) hr)) (fun hf => (fun hn => hn hf) h4))) h

/-- info: 'Whiel.Synthesis.Tests.KernelLratHelper.inf_s199_lrat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inf_s199_lrat

/-- info: 'Whiel.Synthesis.Tests.KernelLratHelper.inf_s199' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inf_s199

end KernelLratHelper
end Tests
end Synthesis
end Whiel
