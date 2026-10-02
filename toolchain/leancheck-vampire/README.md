# Pinned leancheck Vampire

Certification generates Lean proofs with Vampire's `leancheck` output mode.
The repository controls that tool through the `leancheck_vampire` role of
`toolchain.lock.json`:

- `source`: the upstream repository, branch, and commit
  (`vprover/vampire`, branch `leancheck`, commit
  `d3a6306601ef988fb11438019fba192eb0305a2d`).
- `patches`: the checked-in corrections under `patches/`, in the order they
  are applied. Each entry records its SHA-256, the SHA-256 of every source
  file before and after that patch, and the fixed author, date, and message
  used to commit it. Each entry's `before_sha256` is the tree the previous
  entry leaves behind, so the series is applicable in the locked order and
  no other. Committing with the fixed identities makes every applied commit
  hash reproducible, so Vampire's own `--version` output names the last
  commit of the series.
- `build`: the exact configure and compile commands. `SOURCE_DATE_EPOCH` is
  the last patch commit's date.
- `probe`: the machine-readable version probe.
- `regression`: the emitter-regression script and the fixture root; every
  locked patch must have a fixture family under it.
- `sha256` and `platforms`: the resolved binary digest and build identity
  for each supported platform.

The checkout under `toolchain/build/` is ignored, disposable build
state. The lock, the patches, and the fixtures here are the pin. Keep the
previous checkout until a new one probes clean; the locked path names the
abbreviated commit of the last patch, so the two never collide.

## Commands

Build (or rebuild with `--force`) the pinned binary into the locked path:

```text
python3 scripts/build_leancheck_vampire.py --force
```

Probe the locked binary's identity:

```text
python3 scripts/probe_leancheck_vampire.py --json
```

Run the emitter regression fixtures against the locked binary, including
Lean elaboration of the preserved outputs:

```text
python3 scripts/check_leancheck_emitter.py
```

All three fail closed on a missing patch, a patch or source digest
mismatch, an applied commit that differs from the lock, a binary whose
digest or version does not match the lock, or an unsupported platform.

## The corrections

No generated proof is rewritten after the fact, and no `whiel_synth`
Python transform is ported. Each patch has its own fixture family under
`fixtures/`, holding the preserved uncorrected output, the corrected one,
and the exact problem and arguments that produce them.

### `patches/0001-leancheck-rectify-retained-binders.patch`

Changes only `LeanChecker::rectify` in `Shell/LeanChecker/LeanChecker.cpp`.
Rectification drops every quantified variable that does not occur in its
quantifier body. The emitter built its generic
`have rN (P : ...) : (∃ x y, P x y) ↔ (∃ x' y', P x y)` helper over every
binder of the original quantifier, so a dropped binder was substituted by a
variable with no in-scope name (printed as `default`) or by the name of a
surviving binder, and the generated proof did not elaborate. The helper now
ranges over the retained binders only and is skipped when the substitution
is the identity on them; the emitted
`simp only [forall_const, exists_const]` step already removes dropped
binders from the premise. See `fixtures/rectify-retained-binders/`.

### `patches/0002-leancheck-definition-symbol-arity.patch`

Changes `Definizator::scanVars` in `Shell/TweeGoalTransformation.cpp` and
`LeanChecker::functionDefinitionIntroduction` in
`Shell/LeanChecker/LeanChecker.cpp`.

The twee goal transformation (`tgt=full`, used by several `casc_2025`
strategies) introduces a fresh symbol for a goal subterm and adds the
defining equation. `scanVars` collected the subterm's term variables into
`_termVars` but appended a different, never-populated stack to `_allVars`,
so `_allVars` held the type variables alone — none, for a first-order
problem. Three things followed from that empty stack: the
"is the definition worth making" test `t->weight() > _allVars.size()+1`
passed for every non-ground compound subterm; the symbol was created with
arity `_allVars.size()`, that is zero, while its `OperatorType` was built
over `_termVarSorts` and so had the subterm's real arity; and the defining
term was built with no arguments. The emitted definition was therefore
`! [X,Y] : (sK(X,Y) = sF41)` for a *constant* `sF41` declared
`ι → ι → ι` — an equation that is not a conservative definition of `sF41`
at all, and a Lean rendering that could not elaborate
(`_sF41 has type ι → ι → ι but is expected to have type ι`). The
release-build assertions that would have caught it (`ASS_EQ` in `scanVars`,
`ASS(fun->arity() == variableMap.size())` in the emitter) are compiled out.
`scanVars` now appends `_termVars`, which is what the surrounding code and
the higher-order branch already assume.

That `TweeGoalTransformation.cpp` hunk is byte for byte upstream commit
`c098eb89a3dcb7a1e5fcd139b75f84a1b144648c` (Marton Hajdu, 2026-05-07,
"Remove secondary term variables stack to prevent unsoundness"); the
`leancheck` branch base `d3a630660` simply predates it, so the patch
carries a fix the branch has not caught up with rather than a divergence
from upstream. Upstream `5f498d2f1015f9fc96a716812eb35f2e63e5534c` ("Fix
Twee goal transformation inference type", 2026-08-07) touches the same
file after it and is not carried here; examine it at the next rebase.

The emitter half is this repository's own, and is the robustness fix that
does not depend on the first. `functionDefinitionIntroduction` took the
`let`'s binder list from a traversal of the equation's variable map —
ordered by that map's allocation, and sized by the equation's variables
rather than by the symbol's arity. It now reads the binders off the
introduced symbol's own application inside the equation, and emits them
without `outputVariables`'s index sort, so the declaration, the `let`, the
defining equation's `fun … => rfl`, and every later use agree on how many
parameters the symbol has and in what order by construction. The order
matters on its own: the twee transformation fixes a symbol's parameters by
first occurrence in the defined subterm, so a goal subterm that visits a
higher-indexed variable first — `f(Y, g(X))` — yields a parameter list that
is not ascending in the variable index, and sorting it would permute the
binders against the defining equation and leave the `rfl` unprovable. An
equation that does not apply the introduced symbol to variables is emitted
as before and simply fails to elaborate, rather than being papered over
with a guessed binder list.

See `fixtures/definition-symbol-arity/`.
