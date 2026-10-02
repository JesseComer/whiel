# `rectify` retained-binder regression fixtures

Each case directory preserves one leancheck job that exposed the
default-binder defect of the unpatched emitter:

- `problem.p`: the exact TPTP problem, byte for byte.
- `arguments.json`: the exact Vampire arguments; the check runs the binary
  with the case directory as working directory so the portfolio log lines
  name `problem`.
- `unpatched.lean`: the raw standard output of the pinned source before
  (commit `d3a630660`, binary SHA-256
  `3a2bfd98408318cee2c0cf36358ea7869a27bff08d1952c12b146e4a19f8e86f`).
  Its last `rectify` step contains helpers such as
  `(∃ v5 v6, P v5 v6) ↔ (∃ v5 default, P v5 v6)` and fails to elaborate
  with `Unknown identifier v6`.
- `patched.lean`: the raw standard output of the locked corrected binary.
  The two outputs differ only inside `rectify` steps and in the
  `-- Version:` trailer, and this one elaborates with the pinned VampLean
  runtime. Adding `0002` to the series left both proofs unchanged and moved
  only that trailer.

| case | origin |
| --- | --- |
| `example1032-maint_clause_3` | legacy campaign `prototype-casc-budget-blockers-r4-20260827`, case `Example1032`, job `maint_clause_3` |
| `example1065-maint_clause_0` | legacy campaign `prototype-casc-budget-blockers-r4-20260827`, case `Example1065`, job `maint_clause_0` |

Lines that vary from run to run (`-- Time elapsed`, `-- Peak memory usage`,
`-- Success in time`, and the temporary proof path) are ignored by
`scripts/check_leancheck_emitter.py`, and the section-variable telescope is
compared as a set because the emitter groups and orders those declarations
by an allocation-dependent traversal. Everything else, including the
`-- Version:` trailer naming the emitting binary, must match exactly. The
uncorrected and corrected outputs differ only inside `rectify` steps and in
that trailer.
