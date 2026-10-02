# leancheck emitter regression fixtures

One directory per emitter defect the pinned patch series corrects, and one
case directory inside it per preserved leancheck job. `family.json` names
the locked patch the family regresses, the defect signature
`scripts/check_leancheck_emitter.py` must find in the uncorrected output
and must not find in the corrected one, the error the uncorrected output
must fail to elaborate with, and — for a family whose correction is
confined to particular proof steps — the step suffix outside which the two
outputs may not differ. Every patch in `toolchain.lock.json`'s `patches`
list must have a family here; the check reports a patch with no family as a
failure.

Each case directory holds:

- `problem.p`: the exact TPTP problem, byte for byte.
- `arguments.json`: the exact Vampire arguments; the check runs the binary
  with the case directory as working directory so the portfolio log lines
  name `problem`.
- `unpatched.lean`: the raw standard output of the pinned source *before*
  that family's patch.
- `patched.lean`: the raw standard output of the locked corrected binary.

Lines that vary from run to run (`-- Time elapsed`, `-- Peak memory usage`,
`-- Success in time`, and the temporary proof path) are ignored, and the
section-variable telescope is compared as a set because the emitter groups
and orders those declarations by an allocation-dependent traversal.
Everything else, including the `-- Version:` trailer naming the emitting
binary, must match exactly — so every `patched.lean` is re-recorded when
the series gains a patch and the built commit changes.

| family | patch | defect |
| --- | --- | --- |
| `rectify-retained-binders` | `0001` | a `rectify` helper binds a variable that rectification dropped |
| `definition-symbol-arity` | `0002` | an introduced `_sF` definition symbol is declared, defined, and used at disagreeing arities |
