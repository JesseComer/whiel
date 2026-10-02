# Benchmark report

```bash
python3 Benchmark/report/build_report.py          # add --no-pdf to skip the PDF
```

One command regenerates everything in this folder, and it reads nothing outside
`Benchmark/`: each case folder's `Input.lean` (the Hoare triple), `Metadata.json`
(title, category, sources, the Datalog programs the case records under `datalog`, and the
optional `explanation`/`preInWords`/`postInWords` reading-aid keys), `Certificate/` (for
the status line only), the generated ledger
`Benchmark/CertificatePlacement.json` (where each certificate's kernel check runs), and the
two hand-edited files here:

* `tags.json` — the short tag vocabulary (what makes a program interesting to database
  people). The three recursion tags are computed by the script; the others are assigned
  per case in `curated.json`.
* `curated.json` — manual tags, prophecy status lists, category assignment, source links,
  hand-written Datalog readings for cases without a recorded program, notes.

A case folder is anything under `Benchmark/` holding both an `Input.lean` and a
`Metadata.json`; everything else is skipped. Adding such a folder is enough for the case
to appear in the rebuilt report, with its automatic tags and the category its metadata
names; it needs no entry in `curated.json`, and a case whose metadata names no known
category is reported as `uncategorized`.

## Status

A case's status is read off its folder and off nothing else:

| Status | Read off |
|--------|----------|
| certified valid | `Certificate/Valid.lean` whose first line is the certificate emitter's marker |
| certified invalid | `Certificate/Invalid.lean` whose first line is that marker |
| solved valid, not yet certified | `Core.json` beside the input, and no emitter-written `Certificate/Valid.lean` |
| solved invalid, not yet certified | `Counterexample.json` beside the input, and no emitter-written `Certificate/Invalid.lean` |
| open | neither a certificate nor a frozen record in the case folder |

A certificate outranks the record it was built from, so a certified case keeps its
certified status although its record stands beside it. A solved status says that the answer
is known and its record is frozen, never that anything has been kernel-checked.

A hand-written certificate is not a certified status. What the metadata expects of a case
(`expectedVerdict`, or `currentClassification` in the older schema) is printed beside the
status as the expectation, never in place of it.

Where a certificate is checked is measured, not curated. `scripts/place_certificates.py`
elaborates every emitter-written certificate on its own and writes what it found to
`Benchmark/CertificatePlacement.json`: per case, a digest of the certificate tree, the peak
resident memory the kernel check reached (`peakKb`), whether that fits the library build's
limit, and the note naming the peak, the file and the limit when it does not. The report reads
that ledger and nothing else on the question; a case with no entry, or a missing ledger, is
checked inside the library build.

A case the ledger records with `"fits": false` keeps its certificate out of the library root,
so its kernel check does not run in the watched library build. Such a case is counted as
certified in the status table like any other, and the line under that table says how many
cases are checked outside it; the case's own section reads `certified …
(certificate checked outside the library build)` and prints the ledger's note under its own
lead-in, `Placement note: …`, followed by the measured peak in megabytes. The lead-in matters:
without it the note reads as a verdict on the certificate rather than on its size.
`inventory.json` carries the flag (`certificate_outside_library`), the note
(`certificate_note`) and the peak in KB (`certificate_peak_kb`, `null` when the ledger
recorded none). A certificate that is re-emitted lighter returns to the library as soon as the
placement script measures it again — no metadata key and no hand edit is involved. A ledger of
the older version, written before the peak was measured, is still read; it simply carries no
peak to print.

## First-order reading of PRE/POST

`ra_to_fol.py` parses each case's `inputPre`/`inputPost` (the `programAssert!`
relational-algebra assertion) and translates it, mechanically, to a first-order-logic
formula: relation names become predicates, `π` becomes `∃` over the dropped columns
(unifying away a `σ[#i = #j]` equality wherever that is sound, rather than leaving a
dangling `y = z`), `σ` becomes a conjunct, `∪`/`∖`/`×` become `∨`/`∧¬`/`∧`, and
`A (⊆|=|≠) B` becomes `∀x̄. (φ_A → φ_B)` / `↔` / its negation. Every case's PRE and POST
must translate; a construct the module cannot handle fails the whole build rather than
being skipped silently, per `Benchmark/CORPUS.md`. The report prints the result under the
label "First-order reading of PRE/POST, translated mechanically from the
relational-algebra assertion in Input.lean" — a reading aid only, never a replacement for
the relational-algebra text, which remains the authority. `Benchmark/report/tests/test_ra_to_fol.py`
covers the parser and translation rules by hand-worked example, every case in the live
tree, and semantic agreement between the relational algebra and the translated formula on
random finite instances.

## Outputs

* `benchmark_report.pdf` / `.tex` — status summary, overview table with hyperlinks, tag
  vocabulary and index, one section per case (title, category, kind, status, sources,
  tags, Datalog, the first-order reading of PRE/POST, Hoare triple).
* `benchmark_report.html` — the same content on one page with a multi-tag filter (tick
  tags; "all" = every ticked tag must hold, "any" = at least one), a category filter and a
  search box. Open it in a browser (it is self-contained).
* `benchmark_tags.csv` / `.xlsx` — one row per case, one column per tag; use the AutoFilter
  on the tag columns to select cases carrying several tags (the filters combine with AND).
  The `.xlsx` is written only when `openpyxl` is installed, and is not tracked.
* `inventory.json` — the machine-readable record of everything above. It also carries the
  result of the duplicate scan (alpha-equivalent triples, same command with a different
  claim, shared loop segments and Datalog programs), which the build prints to the console;
  the report itself has no duplicates section.

The outputs are deterministic: they carry no build date and no absolute path, so two runs
over the same corpus produce byte-identical files, and a run in a copy of `Benchmark/`
alone produces the same bytes as a run in the repository.

Requires `pdflatex` (TeX Live) for the PDF and `openpyxl` for the `.xlsx`.

## Tests

```bash
python3 -m unittest discover -s Benchmark/report/tests
```

The tests cover input parsing, the automatic tags, the status derivation, the isolation
property (a build in a copy that holds nothing but `Benchmark/`), determinism, and adding
and removing a case folder. Certificate placement is covered by building a copy of the corpus
with a ledger written into it: a case the ledger keeps outside the library build is reported
as such, with its note under its lead-in and with its measured peak, in the PDF source, the
HTML and `inventory.json`, the status counts are unchanged, a ledger of the older version that
records no peak still builds, and removing the ledger puts every case back inside. The
committed outputs are checked against the committed ledger as well. One further property is checked against the
corpus itself: the Datalog text a case records in its `Metadata.json` under a kernel-checked
provenance is, rule for rule, the text its fidelity module states inside `datalog![ … ]` — so
no block is called kernel-checked that the kernel never saw. The first-order translator
(`ra_to_fol.py`) has its own test file, `tests/test_ra_to_fol.py`, described above.
