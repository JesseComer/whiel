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
