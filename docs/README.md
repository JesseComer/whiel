# Collaborator guide

Start with the [campaign quickstart](campaign-quickstart.md). It runs
AgentHoudini, the current collaborator product, on `Benchmark/<ID>/Input.lean`,
with native Codex or Claude and an independently checked certificate for each
solved input.

| Need | Guide |
| --- | --- |
| First run, one input or a campaign | [Quickstart](campaign-quickstart.md) |
| Standalone Lean coding-agent baseline | [Baseline section of the root README](../README.md#lean-coding-agent-baseline-direct-lean) |
| Every accepted option and default | [CLI reference](cli-reference.md) |
| Local/Linux setup, model selection and login | [Providers and authentication](providers-and-auth.md) |
| The six query tools, submission and legacy skill ideas | [Tools and skills](tools-and-skills.md) |
| The proposer API and customization entry points | [Proposer API](proposer-api.md) |
| What collaborators may change | [Code and trust boundaries](collaborator-boundaries.md) |
| Read results, diagnose failures and preserve evidence | [Results and troubleshooting](results-and-troubleshooting.md) |

The paper specifies the proposal method and the underlying checking
algorithm. The maintained [proposer API](proposer-api.md) records the current
query/submission contract. This guide explains the current implementation and
limits.

The reference includes the integrated resource guards, numeric selectors and
consultation controls. Their scopes and limitations are explicit; sampled space
checks are not disk quotas.
This guide does not install anything, start a campaign or authorize publishing
third-party code. See the [dependency notes](collaborator-boundaries.md#third-party-dependencies)
for upstream attribution and the pinned VampLean dependency.
