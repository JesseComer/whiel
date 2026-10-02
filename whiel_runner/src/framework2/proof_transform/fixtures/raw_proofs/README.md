# Raw Vampire proof fixtures

Each `<Example>/<job>/leancheck.lean` under this directory is one complete,
byte-for-byte unmodified `leancheck.lean` as the pinned Vampire emitted it for
that job of that benchmark example, before any proof transform runs. No such
raw file is hand-written or hand-edited.

`Example5001/term_check/projected_trace.lean` is a separate structural fixture,
copied verbatim from lines 213–238 of the TermCheck proof retained by the
validity Lake diagnostic dated 2026-09-29. The complete selected source has
SHA-256 `136c46089e06812ce860d40faed38aba88ad2e29c6d4b8910f00adec3677d1f1`.
Its receipt records a LocalPrenex version 1 fallback for step79. The nearest
ancestor contains `Xor'`, while the later inference has expanded it; the
version 2 recognizer records a miss. The fragment retains the complete
ancestor lineage, skolemisation, projected targets and inference tail. It is
neither a complete raw proof nor an independently checked theorem.

They exist so `checked_in_raw_proofs` in `../../tests.rs` has a small,
checked-in corpus of genuine raw solver output to run
`canonical::canonicalize` over, independent of whatever solver evidence a
given certificate under `Benchmark/` currently carries.

Every file was matched to its example and job, and its provenance confirmed
by canonicalizing it and comparing the result against the corresponding
`Benchmark/<Example>/Certificate/VampireProofJobs/<Job>.lean` module (the
packaged, transformed proof that module was built from): the two agree on
their final `exact stepN` line, and, on jobs the clause-projection and
local-prenex rewrites left untouched, agree exactly from `section vamproof`
onward.

The fixture spans:
- `Example0001` — the ordinary case, one job of each kind (`init_clause_*`,
  `maint_clause_*`, `term_check`).
- `Example5010` — a case whose prophecy schema (`Core.json` rows sourced from
  a `yp_`-prefixed relation) is exercised by the loop.
- `Example4036` — a case whose schema has named domain constants (the
  `_ksa`/`_ksb`/`_ksc` string constants visible in its proofs), covering one
  job of each kind.

## Refreshing

To refresh a file here (for example after a solver or pipeline change),
rebuild the certificate's evidence and copy the surviving raw proof back in
place, unmodified:

```
certificate build --evidence <evidence-dir> <example>
cp <evidence-dir>/<example>/jobs/<job>/leancheck.lean \
   whiel_runner/src/framework2/proof_transform/fixtures/raw_proofs/<Example>/<job>/leancheck.lean
```

Re-run the provenance check described above (canonicalize the new file and
compare its final `exact stepN` line, and section body where unrewritten,
against the matching `VampireProofJobs` module) before committing the
refreshed fixture.
