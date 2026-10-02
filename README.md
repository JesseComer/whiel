# Whiel

Whiel verifies imperative relational programs against Hoare specifications.
It combines an LLM-based proposer of invariants or counterexamples with a
symbolic verifier built using Lean and Vampire. An independent certifier
constructs Lean proofs of the original specification or its negation, without
further LLM assistance. Search acceptance and Lean certification are distinct
results.

The repository includes **86 relational verification tasks**, with certified
reference answers for all of them: **69 valid and 17 invalid**. Applications
include recursive query equivalence and containment, evaluation strategies,
incremental view maintenance, and view-based query rewriting.

- **[Reproduction guide](REPRODUCIBILITY.md):** installation, builds, paper
  experiments, certification, and the Direct Lean baseline.
- **[Certificate audit guide](AUDIT.md):** start here to understand what a
  certificate proves, which definitions to inspect, and what must be trusted.
- **[Benchmark guide](Benchmark/CORPUS.md):** tasks, reference answers, sources,
  and benchmark maintenance.

## Repository layout

| Directory | Contents |
| --- | --- |
| [Whiel/](Whiel/) | Command language, semantics, Hoare logic, verification and certification support. |
| [Databases/](Databases/) | Schemas, relations, instances, relational algebra and other database foundations. |
| [whiel_runner/](whiel_runner/) | Rust controller, verifier, certificate construction and command-line tools. |
| [agent_houdini/](agent_houdini/) | Python proposer, provider integration, experiment launcher and task pool. |
| [Benchmark/](Benchmark/) | All 86 tasks, certified reference answers and the benchmark report. |
| [toolchain/](toolchain/) | Pinned solver sources, patches and build support. |

## Getting started

The [reproduction guide](REPRODUCIBILITY.md) gives copy-paste commands to run
the paper experiments and read their results. It lists the fixed parameters of
the reproduction wrappers. Fresh experiment records go under ignored
`artifacts/`; benchmark maintenance is documented separately.

<!-- Preserve inbound links from the existing documentation. -->
<a id="linux-setup-and-builds"></a>
<a id="search-and-paper-experiment-settings"></a>
<a id="token-free-replay-checks"></a>
<a id="certification-and-shipped-proof-checks"></a>
<a id="lean-coding-agent-baseline-direct-lean"></a>
<a id="3-log-in"></a>
<a id="results-benchmark-report-and-further-documentation"></a>

- [Whiel search: setup, login and model stages](REPRODUCIBILITY.md#whiel-search)
- [Whiel-OneRound](REPRODUCIBILITY.md#whiel-oneround)
- [Direct Lean and its axiom audit](REPRODUCIBILITY.md#direct-lean)
- [Certification](REPRODUCIBILITY.md#certification)
- [Benchmark maintenance](Benchmark/CORPUS.md) and
  [transcript replay checks](docs/analysts-guide.md#7-checking-a-replay-against-its-transcript)

## Further documentation

- [CLI reference](docs/cli-reference.md)
- [Providers and authentication](docs/providers-and-auth.md)
- [Result schemas and analysis](docs/analysts-guide.md)
- [Tools and skills](docs/tools-and-skills.md)
- [Proposer API](docs/proposer-api.md)
- [Certificate compilation](docs/certificate-compilation.md)
- [Documentation index](docs/README.md)

## Contributing Style

For Lean files in this repository, prefer:

- `namespace`-organization (`Schema`, `Instance`,
  `RelAlg`, etc.).
- Never let a `namespace` cross a major section boundary:
  close it before the next section header, then reopen.
- Do not use one high-level `namespace` to wrap an entire
  file when the file contains section headers.
- Put each section header outside all namespaces; open the
  namespace immediately after the header.
- Put a full empty line between section headers and
  namespace openings, between namespace openings and the
  first declaration, and between the final declaration and
  namespace closings.
- `variable` declarations should be scoped locally to the
  namespace/section where they are used.
- Narrow assumptions (only include the typeclasses
  needed by the local block).
- Do not use `sorry`, `admit`, `classical`,
  `noncomputable`, or `partial`.
- The `partial` prohibition does not apply to notation
  files, where syntax expanders may need Lean metaprogram
  recursion.
- Keep code lines at or below the section-bar width
  (currently 60 characters).
- The standard major-section header format:

```lean
------------------------------------------------------------
-- Section Title
------------------------------------------------------------
```

- Concise comments (`/- ... -/`) on key
  definitions and theorems.
- Prefer plain `/- ... -/` comments over
  `/-- ... -/` doc comments.
- For comments above definitions, use exactly one of:
  - One-line form (if it fits width):
    `/- Short comment. -/`
  - Multi-line form (if it does not fit):
    open/close markers on their own left-aligned lines,
    with content indented one level (i.e., two spaces).

### Naming Conventions

For database formalizations, prefer the following variable names:

- `D`: domain type.
- `A`: relation-name type.
- `F`: function-name type.
- `α`: attribute-name type.
- `Γ Δ Θ`: schemas, with `Γ` usually the ambient or base
  schema and `Δ`/`Θ` for related or extended schemas.
- `Λ`: first-order signatures.
- `X Y Z`: relation symbols, usually as schema members.
- `f g`: function symbols.
- `n m k`: arities or natural-number indices.
- `t u v`: tuples.
- `R S T`: finite relations or sets, by local context.
- `Q`: domain-of-quantification or active-domain-style
  subsets of `D`.
- `C`: finite sets of constants.
- `I J K`: unnamed instances over schemas.
- `M N`: finite structures.
- `e`: relational algebra expressions.
- `q`: RelCalc queries.
- `φ ψ χ`: RelCalc or FOL formulas, and relational
  algebra selection conditions.
- `P`: Datalog programs.
- `r`: Datalog rules.
- `σ τ`: variable assignments.
- `h...`: proof hypotheses, named by content when useful,
  such as `hExt`, `hMem`, or `hAr`.

When more names are needed, add natural-number subscripts,
for example `I₁`, `I₂`, `A₁`, or `A₂`.
Avoid suffixes that duplicate type information already
present in the declaration, such as `IΓ` or `IΔ`; write
`(I : Instance D Γ)` and `(J : Instance D Δ)` instead.

### Top-of-file Specification Notes

For files that define a key language, semantics,
construction, translation, or metatheorem, add a short block
comment after the imports and before the first section
header. This comment should help a reader check the intended
specification and the main correctness path without reading
every construction lemma.

Use the same plain block-comment style as other comments:

```lean
/-
  This file specifies ...

  Key definitions include:
    * `Namespace.Declaration`

  The main construction is:
    * `Namespace.construction`

  Correctness is proven by:
    * `Namespace.theorem_name`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/
```

Guidelines:

- Mention only the declarations that are central to the
  specification or correctness path. Do not list routine
  helper definitions, supporting lemmas, or every theorem in
  the file.
- Top comments should orient readers at a high level, not
  inventory the file. If `Instance.update` is listed, for
  example, assume its local lookup and algebraic lemmas live
  nearby.
- For translation files, call out the main translation
  function or construction, and any key correctness,
  equivalence, preservation, or soundness theorems.
- Complex constructions should be presented with an explicit
  specification of what correctness means and a theorem
  proving that the construction meets that specification.
  Ideally, structure the file as:
  1. specification details;
  2. construction;
  3. proof of correctness.
  This ordering is preferred, not mandatory; use a different
  order when it makes the file easier to read.
- For complex constructions, include a very short
  description of the construction idea in the top comment.
  When possible, reference standard terminology from the
  literature.
- Put declaration names in backticks, including fully
  qualified namespaces when helpful, e.g.
  `` `Program.MinimalModel` `` or
  `` `FOL.Semantics.evalTermList_toList` ``.
- Group declarations by role when that helps readability:
  key definitions, construction, correctness, or key
  theorems.
- It is fine to end with a catch-all sentence saying that
  intervening definitions and lemmas are construction,
  helper, or proof support.
