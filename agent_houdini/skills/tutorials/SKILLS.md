# Tutorial Skills Index

Flat, markdown-based tutorial library. All tutorials are loaded into every synthesis prompt (Claude-skills style, no retrieval).

## Provenance

Every concrete invariant quoted in these files comes from one of the following 6 CEGIS runs:

```
artifacts/runs/synth/postfix_high_20260422_031956/cegis_nomcp/logs/
├── tc_left__spec_left__naive.log                           ── success, 3 iter
├── tc_left__spec_left__seminaive.log                       ── success, 4 iter
├── tc_nonlin__spec_nonlin__naive.log                       ── success, 6 iter
├── tc_right__spec_left__naive.log                          ── success, 4 iter
├── tc_right__spec_right__naive.log                         ── success, 2 iter
└── cegis_nomcp_retry_high/logs/tc_nonlin__spec_left__naive.log  ── success, 1 iter (retry-high variant)
```

All six successful invariants are reproduced verbatim in the walkthrough files.

## Leakage scope — important

The 6 source benchmarks are variants of classic TC. Their verified invariants are **structurally identical** (modulo renaming `E` ↔ `base`) to the answers for:

- `gen-tc-left`, `gen-tc-right`, `gen-tc-nonlinear`
- Their `-seminaive` variants
- Any `*_tc_left*`, `*_tc_right*`, `*_tc_nonlinear*` equivalence-pair benchmark

**Do not use this skill set to synthesise invariants for those benchmarks** — you will be evaluating against training data. Safe targets: programs whose bodies are structurally different from linear/nonlinear TC (e.g. multi-IDB programs, PTA, BFS/worklist, same-generation, chain-3, reach/bidir, etc.), and programs that use different EDB schemas (arity ≠ 2, multiple EDBs beyond `E` and `R`).

The `method-*` files teach general VC reasoning and are leakage-safe even on the above benchmarks.

## Method tutorials (general, leakage-safe)

- [method-ra-syntax](method-ra-syntax.md) — RA operators, prefix-operator parenthesisation, right-nested `&`.
- [method-init-vc](method-init-vc.md) — Init VC: trace the pre-block concretely.
- [method-maint-vc](method-maint-vc.md) — Maint VC: every clause needs a supporter.
- [method-term-vc](method-term-vc.md) — Term VC: each clause must do work under `¬G`.

## Pattern skills (structural templates, some TC-specific)

- [pattern-postfix-naive](pattern-postfix-naive.md) — The 4-clause postfix template: def-eq, `T ⊆ R`, `S ⊆ R`, closure on `R`.
- [pattern-postfix-subset](pattern-postfix-subset.md) — When def-eq fails, replace `S = BODY(T)` with `BODY(T) ⊆ S`.
- [pattern-seminaive-coupling](pattern-seminaive-coupling.md) — Semi-naive subset coupling `BODY(T) ⊆ (T ∪ D)` + combined bound.
- [pattern-body-spec-bridge](pattern-body-spec-bridge.md) — Dual def-eq trick when program body and Q use different RA shapes.
- [pattern-counterexample-analysis](pattern-counterexample-analysis.md) — Reading Vampire counterexamples.

## Example walkthroughs (concrete programs)

- [example-tc-right-naive](example-tc-right-naive.md) — Easiest case (2 iter, 117 s). `tc_right__spec_right__naive`.
- [example-tc-left-naive](example-tc-left-naive.md) — Medium (3 iter, 126 s). `tc_left__spec_left__naive`.
- [example-tc-nonlinear-naive](example-tc-nonlinear-naive.md) — Hard (6 iter, 303 s). Uses subset-def-eq. `tc_nonlin__spec_nonlin__naive`.
- [example-tc-seminaive](example-tc-seminaive.md) — Semi-naive (4 iter, 133 s). `tc_left__spec_left__seminaive`.
- [example-tc-cross-spec](example-tc-cross-spec.md) — Body/spec mismatch via two different bridging techniques: dual def-eq (`tc_right__spec_left__naive`, 4 iter) and mixed closure `proj(S × R) ⊆ R` (`tc_nonlin__spec_left__naive` retry-high, 1 iter).
