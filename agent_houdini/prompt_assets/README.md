# prompt_assets
-- Author: Claude

The proposer's reference, rendered at the head of every prompt by
`prompt.py`, ahead of C's structured presentation of the push. It states
the verification goal, how the leveled checks work, the clause grammar,
how to read the push and its verdicts, the queries, and submission
discipline. It does not coach: the method-level material (how to build a
Core in layers, clause patterns for particular loop shapes, a worked
example) lives in the skill library under `agent_houdini/skills/`, served
through `get_skill` only when a run enables it, so that a run without
skills reads the reference alone and the library's contribution can be
measured.

| File | Rendered on | Contents |
|---|---|---|
| `00-framework.md` | every consultation, unconditional | mission, the verification framework (ladder, checks, Core, death/drops), the clause language (prophecy, grammar, common mistakes), how to read the push (including verdict meanings and responses), the queries, submission discipline (the two proposal kinds, host limits, the Never list) |

Editing this file changes the prompt, so regenerate the golden fixtures
(`python3 -m agent_houdini render-prompt` on `example0001_consultation.json`
and `example2004_consultation.json`, plus `default_prompt.txt`) in the same
checkpoint; `tests/test_prompt.py` compares them byte for byte.

Since API 3.1.0 the verifier publishes the run's data and no explanation of its
own, so every rule the agent needs is stated here: what a clause may be, the two
proposal kinds and the instance shape, the checks and the levels, the death and
drop rules, the protected rows, and how a host limit refuses a submission. A
rule that leaves this directory leaves the prompt.

This directory is C-owned prompt material. It is explanation, never evidence:
nothing here is a verifier fact, a proof, or an authority for any decision. The
authoritative statements live in the pinned reports and in the controller push;
when they disagree with this text, this text is the bug.
