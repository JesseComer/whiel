# Author: Fangzhu Shen
"""Golden rendered prompts, push selection, and the offline render-prompt tool."""

import io
import json
from pathlib import Path
import re
import tempfile
import unittest

from agent_houdini.json_wire import decode, encode
from agent_houdini import prompt as prompt_module
from agent_houdini import render as render_module
from agent_houdini.prompt import (
    ASSET_ORDER, FIRST_BUDGET_BYTES, LATER_BUDGET_BYTES, UNCONDITIONAL_ASSETS,
    asset_text, clause_spelling, is_first_consultation, render_prompt,
)


FIXTURES = Path(__file__).resolve().parents[1] / "fixtures"
EXAMPLE0001 = FIXTURES / "example0001_consultation.json"
EXAMPLE2004 = FIXTURES / "example2004_consultation.json"
# The heading of the single unconditional asset; if it renders, the whole
# verification framework, clause grammar and push reference are present.
UNCONDITIONAL_HEADINGS = (b"# Your role",)


def recorded(path=EXAMPLE0001):
    document = decode(path.read_bytes())
    return document["observation"], encode(document["response_example"])


class GoldenPromptTests(unittest.TestCase):
    """A prompt change has to show up here as a reviewable diff."""

    def test_recorded_example0001_first_consultation_matches_the_golden(self):
        expected = (FIXTURES / "example0001_prompt.txt").read_bytes()
        prompt, source = render_module.render(EXAMPLE0001)
        self.assertEqual(source, EXAMPLE0001)
        self.assertEqual(prompt, expected)

    def test_minimal_push_matches_the_golden(self):
        expected = (FIXTURES / "default_prompt.txt").read_bytes()
        observation = decode((FIXTURES / "default_push.json").read_bytes())
        example = (FIXTURES / "default_example.json").read_bytes().strip()
        self.assertEqual(render_prompt(observation, example), expected)

    def test_recorded_example2004_later_consultation_matches_the_golden(self):
        """A real populated later push, not an empty one.

        The empty recorded push is the smallest tail C ever renders, so pinning
        only that one hid what a real later consultation held: a populated push
        renders its task text twice in the presentation and names a clause per
        line of the identity tail.
        """
        expected = (FIXTURES / "example2004_prompt.txt").read_bytes()
        prompt, source = render_module.render(EXAMPLE2004)
        self.assertEqual(source, EXAMPLE2004)
        self.assertEqual(prompt, expected)

    def test_a_first_consultation_stays_within_its_byte_aim(self):
        prompt, _ = render_module.render(EXAMPLE0001)
        self.assertTrue(is_first_consultation(recorded()[0]))
        self.assertLessEqual(len(prompt), FIRST_BUDGET_BYTES)
        # All four manual assets fit on an input's opening consultation, and the
        # prompt coaches nothing: no strategy layer, no worked example.
        for heading in UNCONDITIONAL_HEADINGS:
            self.assertIn(heading, prompt)
        self.assertNotIn(b"# Strategy", prompt)
        self.assertNotIn(b"# Worked example", prompt)
        self.assertNotIn(b"# Skills", prompt)

    def test_a_populated_later_consultation_keeps_the_whole_manual(self):
        observation, _ = recorded(EXAMPLE2004)
        prompt = (FIXTURES / "example2004_prompt.txt").read_bytes()
        self.assertFalse(is_first_consultation(observation))
        self.assertGreater(len(encode(observation)), 10 * 1024)
        self.assertTrue(observation["feedback"]["core"])
        self.assertTrue(observation["feedback"]["pending"])
        self.assertLessEqual(len(prompt), LATER_BUDGET_BYTES)
        for heading in UNCONDITIONAL_HEADINGS:
            self.assertIn(heading, prompt)

    def test_a_correction_round_is_not_a_first_consultation(self):
        observation, example = recorded()
        observation = {**observation, "correction": {
            "schema_version": 4, "binding": {"correction_ordinal": 1},
            "diagnostics": [{"code": "wrong_response_binding",
                             "message": "The response binding does not match the exact current consultation.",
                             "item_index": None, "path": None}]}}
        prompt = render_prompt(observation, example)
        self.assertFalse(is_first_consultation(observation))
        self.assertLessEqual(len(prompt), LATER_BUDGET_BYTES)
        self.assertIn(b"wrong_response_binding", prompt)
        # The explanation persists across rounds: the role, the prophecy schema
        # and the checking procedure are present on every later consultation.
        for heading in UNCONDITIONAL_HEADINGS:
            self.assertIn(heading, prompt)

    def test_no_push_is_large_enough_to_drop_the_unconditional_assets(self):
        """The budget may take the strategy layer; it may never take the rules.

        A push far past either aim is rendered whole, with the role, the clause
        grammar and the checking procedure still in front of it.
        """
        observation, example = recorded(EXAMPLE2004)
        feedback = observation["feedback"]
        feedback = {**feedback,
                    "pending": feedback["pending"] * 24,
                    "last_round": feedback["last_round"] * 24}
        swollen = {**observation, "feedback": feedback}
        prompt = render_prompt(swollen, example)
        self.assertGreater(len(prompt), LATER_BUDGET_BYTES)
        for heading in UNCONDITIONAL_HEADINGS:
            self.assertIn(heading, prompt)
        self.assertEqual(len(UNCONDITIONAL_ASSETS), len(UNCONDITIONAL_HEADINGS))

    def test_a_configured_skill_library_is_listed_and_an_absent_one_leaves_no_trace(self):
        from agent_houdini.skills import SkillCatalog

        observation, example = recorded()
        library = SkillCatalog.from_directory(Path(__file__).resolve().parents[1] / "skills" / "v1")
        text = render_prompt(observation, example, skills=library).decode("utf-8")
        self.assertIn("# Skills", text)
        self.assertIn("read with `get_skill` by id", text)
        self.assertIn("    ladder-strategy  —  How to build a Core in layers", text)
        self.assertIn("[applies: semi-naive or frontier loops]", text)
        self.assertNotIn("phase-flags", text)
        self.assertNotIn("example-closure-other-side", text)
        bare = render_prompt(observation, example).decode("utf-8")
        self.assertNotIn("# Skills", bare)
        self.assertNotIn("get_skill", bare)
        disabled = render_prompt(observation, example, skills=SkillCatalog()).decode("utf-8")
        self.assertEqual(disabled, bare)


class PushSelectionTests(unittest.TestCase):
    def test_the_structured_sections_state_the_task_relations_and_budget(self):
        prompt, _ = render_module.render(EXAMPLE0001)
        text = prompt.decode("utf-8")
        for expected in ("# Task Example0001 — consultation 1",
                         "o:p::S        S             op_zS",
                         "y:p::T        T∞            yp_zT",
                         "the exit value of o:p::T",
                         "# Current Core (0 clauses)", "# Pending clauses (0)",
                         "# Last round (0 clauses)",
                         "about 240 seconds of search budget remain"):
            self.assertIn(expected, text)
        # Check rows and refutation history are the agent's own queries now that
        # every identity carries its clause text; the push renders neither.
        self.assertNotIn("# Refutations on record", text)
        self.assertIn("call `history` for one clause's record", text)

    def test_the_relation_table_says_which_relations_an_instance_lists(self):
        """The input schema is not published, so C derives it from the keys.

        An instance is over the ordinary, unindexed, non-flag relations
        (`Whiel/Concrete/WhielNames.lean`, `IsRawInput`); a prophecy copy, an
        indexed preprocessing copy and a control flag are outside it.
        """
        for key, name in (("o:p::E", "p::E"), ("o:a::T", "a::T"),
                          ("y:p::T", None), ("y:a::T", None),
                          ("o:f::1", None), ("o:p:s:R", None), ("nonsense", None)):
            self.assertEqual(prompt_module.instance_name(key), name, key)
        prompt, _ = render_module.render(EXAMPLE2004)
        text = prompt.decode("utf-8")
        self.assertIn("in an instance", text)
        self.assertIn("o:a::Path     Path_aux      oa_zPath       a::Path", text)
        self.assertIn("y:p::Path     Path∞         yp_zPath       —", text)

    def test_the_counterexample_kind_is_shown_whole_and_omits_the_clause_members(self):
        prompt, _ = render_module.render(EXAMPLE0001)
        text = prompt.decode("utf-8")
        self.assertIn('"kind": "candidate_counterexample"', text)
        self.assertIn('"input": {"relations": [{"name": "p::E"', text)
        self.assertIn("omits `clauses` and `dropped`", text)
        self.assertIn("Left in empty, `clauses` and `dropped`", text)
        # The grammar's two commonest missing characters, and the escaping
        # warning kept to the one correction that answers it.
        self.assertIn("`⊇` is the commonest: write", text)
        self.assertEqual(text.count("`\\u`-escaped"), 0)

    def test_the_verifier_publishes_data_and_c_owns_every_word(self):
        """The push carries no explanation, and C renders it rather than dumping it.

        The observation as a whole is not in the prompt any more: its task
        text, schema and limits are rendered once in the sections above, and
        only the values the agent must hand back exactly -- identities and drop
        references -- are copied out verbatim at the end.
        """
        prompt, _ = render_module.render(EXAMPLE0001)
        observation, _ = recorded()
        presentation = observation["feedback"]["presentation"]
        self.assertEqual(set(presentation), {
            "schema_version", "task", "ambient_schema", "host_limits",
            "resource_limits", "presentation_digest"})
        self.assertNotIn("note", presentation["resource_limits"])
        self.assertNotIn(encode(observation), prompt)
        self.assertNotIn(b"COMPLETE CONTROLLER PUSH", prompt)
        self.assertNotIn(b"presentation_digest", prompt)
        self.assertIn(b"IDENTITIES AND DROP REFERENCES", prompt)

    def test_the_response_example_and_every_identity_stay_parseable_at_the_end(self):
        """What the agent copies is exact JSON: the example, then each identity
        and drop reference as the push carried it, and nothing else of the push."""
        prompt, _ = render_module.render(EXAMPLE2004)
        observation, _ = recorded(EXAMPLE2004)
        text = prompt.decode("utf-8")
        tail = text[text.index("RESPONSE ENVELOPE"):]
        decoder, index, found = json.JSONDecoder(), 0, []
        while index < len(tail):
            start = tail.find("{", index)
            if start < 0:
                break
            try:
                value, length = decoder.raw_decode(tail[start:])
            except ValueError:
                index = start + 1
                continue
            index = start + length
            found.append(value)
        example = [value for value in found if value.get("kind") == "candidate_clauses"]
        self.assertEqual(len(example), 1)
        self.assertEqual(example[0]["binding"]["validation_ordinal"], 0)
        feedback = observation["feedback"]
        drops = [entry["drop_reference"] for entry in feedback["pending"]]
        for reference in drops:
            self.assertIn(reference, found)
            self.assertIn(encode(reference).decode("utf-8"), tail)
        identities = [value for value in found if set(value) == {"clause_id", "record_digest", "formula_digest"}]
        named = {entry["clause"]["clause_id"] for key in ("core", "pending", "last_round")
                 for entry in feedback[key]}
        self.assertEqual({value["clause_id"] for value in identities}, named)
        for value in identities:
            source = next(entry["clause"] for key in ("core", "pending", "last_round")
                          for entry in feedback[key] if entry["clause"]["clause_id"] == value["clause_id"])
            self.assertEqual(value["record_digest"], source["record_digest"])
            self.assertEqual(value["formula_digest"], source["formula_digest"])
        # The whole observation is not there: no task text, schema or limits after the example.
        self.assertFalse(any("feedback" in value for value in found))
        self.assertNotIn("presentation_digest", tail)
        self.assertLess(len(tail.encode("utf-8")), 8 * 1024)

    def test_an_empty_push_names_no_identity_and_no_drop(self):
        prompt, _ = render_module.render(EXAMPLE0001)
        text = prompt.decode("utf-8")
        self.assertIn("    none: the push names no clause yet", text)
        self.assertIn("    none: no pending clause is authorized for a drop", text)
        self.assertIn("Host limits in force:\n\n    none", text)

    def test_host_limits_in_force_are_listed_in_the_tail(self):
        observation, example = recorded()
        presentation = {**observation["feedback"]["presentation"],
                        "host_limits": [{"limit": "proposal_size", "value": 12},
                                        {"limit": "level_bound", "value": 2}]}
        feedback = {**observation["feedback"], "presentation": presentation}
        text = render_prompt({**observation, "feedback": feedback}, example).decode("utf-8")
        self.assertIn("    proposal_size: 12\n    level_bound: 2", text)

    def test_every_clause_is_shown_with_the_text_the_verifier_admitted(self):
        """Core, pending and last round read the push's own text.

        C keeps no transcript of what it submitted: the source rendered here is
        the verifier's `canonical_source`, and a differing display spelling is
        shown beside it.
        """
        observation, example = recorded()
        def clause(identifier, source, display=None):
            return {"clause_id": identifier, "record_digest": "a" * 64,
                    "formula_digest": "b" * 64, "canonical_source": source,
                    "display": display}
        feedback = {**observation["feedback"],
                    "core": [{"clause": clause(4, "(op_zT = ∅[2])"),
                              "source": "submitted", "level": 0}],
                    "pending": [{"clause": clause(7, "(op_zT ⊆ yp_zT)", "T ⊆ T∞"),
                                 "source": "submitted",
                                 "minimum_level": 1, "current_level": 2,
                                 "drop_reference": {"clause": {"clause_id": 7}}}],
                    "last_round": [{"clause": clause(7, "(op_zT ⊆ yp_zT)"),
                                    "source": "submitted",
                                    "outcome": {"kind": "pending", "level": 2}}]}
        prompt = render_prompt({**observation, "feedback": feedback}, example)
        text = prompt.decode("utf-8")
        self.assertIn("clause 4  level 0  origin submitted", text)
        self.assertIn("        (op_zT = ∅[2])", text)
        self.assertIn("drop_reference: yes", text)
        self.assertIn("        (op_zT ⊆ yp_zT)", text)
        self.assertIn("        displayed: T ⊆ T∞", text)
        self.assertNotIn("initialization check", text)
        self.assertNotIn("# Refutations on record", text)
        self.assertNotIn("C's own transcript", text)
        self.assertNotIn("Keep your own note", text)

    def latest(self, value, **feedback):
        observation, example = recorded()
        merged = {**observation["feedback"], "latest": value, **feedback}
        return render_prompt({**observation, "feedback": merged}, example).decode("utf-8")

    def test_every_kind_of_latest_result_renders_its_own_explanation(self):
        """The verifier names one sub-object after the event's own kind.

        Rendering one kind's sub-object left a rejection and an infrastructure
        failure as a heading with nothing under it, which is the whole of what
        those two events say.
        """
        text = self.latest({"kind": "counterexample_rejected", "counterexample_rejected": {
            "code": "precondition_fails",
            "reason": "the submitted instance does not satisfy the input precondition"}})
        self.assertIn("counterexample_rejected.code: precondition_fails", text)
        self.assertIn("counterexample_rejected.reason: the submitted instance", text)
        self.assertIn("does not satisfy the precondition", text)
        text = self.latest({"kind": "failure", "failure": {
            "origin": "verification", "kind": "solver_failure", "retryable": True,
            "scope": "lane_local", "has_withheld_detail": False, "artifacts": [],
            "withheld_artifacts": 0}})
        self.assertIn("failure.kind: solver_failure", text)
        self.assertIn("failure.scope: lane_local", text)
        text = self.latest({"kind": "postcondition_open",
                            "postcondition_open": {"outcome": "refuted", "attempt": 17}})
        self.assertIn("postcondition_open.attempt: 17", text)

    def test_a_refutation_without_a_retained_countermodel_says_so(self):
        text = self.latest({"kind": "postcondition_open",
                            "postcondition_open": {"outcome": "refuted", "attempt": None}})
        self.assertIn("postcondition_open.attempt: none", text)
        self.assertIn("No countermodel is retained for this refutation", text)
        self.assertNotIn("attempt: None", text)

    def test_last_round_says_when_no_clause_round_produced_it(self):
        """A counterexample round runs no clause epoch and records no outcomes.

        The section then re-shows an older round, which a memoryless proposer
        reads as the verdict on the instance it just sent.
        """
        observation, example = recorded()
        entry = {"clause": {"clause_id": 4, "record_digest": "a" * 64,
                            "formula_digest": "b" * 64,
                            "canonical_source": "(op_zT = ∅[2])", "display": None},
                 "source": "submitted",
                 "outcome": {"kind": "dead", "cause": "refuted",
                             "reason": {"kind": "prophecy_free_initialization_refuted",
                                        "attempt": 9}}}
        feedback = {**observation["feedback"], "last_round": [entry],
                    "latest": {"kind": "counterexample_rejected", "counterexample_rejected": {
                        "code": "malformed", "reason": "source instance omits a required relation"}}}
        text = render_prompt({**observation, "feedback": feedback}, example).decode("utf-8")
        self.assertIn("# Last round (1 clause)", text)
        self.assertIn("which runs no clause round", text)
        # The refuting check's ledger row is the one way back to that check.
        self.assertIn("clause 4  dead, cause refuted, ledger row 9  origin submitted", text)
        empty = {**feedback, "last_round": [],
                 "latest": {"kind": "failure", "failure": {
                     "origin": "verification", "kind": "solver_failure", "retryable": True,
                     "scope": "lane_local", "has_withheld_detail": False,
                     "artifacts": [], "withheld_artifacts": 0}}}
        text = render_prompt({**observation, "feedback": empty}, example).decode("utf-8")
        self.assertIn("recorded no clause outcomes", text)
        self.assertNotIn("No previous round.", text)

    def test_the_budget_is_named_as_this_turn_s_deadline_too(self):
        prompt, _ = render_module.render(EXAMPLE0001)
        text = prompt.decode("utf-8")
        self.assertIn("this turn ends no later than it does", text)
        self.assertIn("the turn is killed with nothing", text)
        self.assertNotIn("not a per-turn allowance", text)

    def test_a_binding_correction_shows_the_exact_keys_the_verifier_named(self):
        observation, example = recorded()
        corrected = {**observation, "correction": {
            "schema_version": 4, "binding": {"correction_ordinal": 1},
            "diagnostics": [{"code": "wrong_response_binding",
                             "message": "Copy the binding object of this consultation's response example exactly.",
                             "item_index": None, "path": "$.binding",
                             "details": {"missing": ["request_digest"],
                                         "unexpected": ["policy_digest"],
                                         "changed": ["consultation_digest"]}}]}}
        text = render_prompt(corrected, example).decode("utf-8")
        self.assertIn("path: $.binding", text)
        self.assertIn("missing: request_digest", text)
        self.assertIn("unexpected: policy_digest", text)
        self.assertIn("changed: consultation_digest", text)
        self.assertIn("This is an envelope refusal", text)
        self.assertIn("The fault is the envelope's own binding", text)
        # The fault the verifier named comes first; the remedy follows it.
        self.assertLess(text.index("missing: request_digest"),
                        text.index("This is an envelope refusal"))

    def test_an_envelope_refusal_elsewhere_does_not_send_the_agent_to_the_binding(self):
        """A stray member or an undecodable document is not a binding fault.

        Leading every envelope refusal with "copy the binding again" sent a
        proposer whose binding was already exact to recopy it and resend the
        same mistake.
        """
        observation, example = recorded()
        for code, path, details in (
                ("malformed_response", "$",
                 {"missing": [], "unexpected": ["clauses", "dropped"], "changed": []}),
                ("malformed_json", None, None),
                ("duplicate_object_key", None, None)):
            diagnostic = {"code": code, "message": "refused.", "item_index": None, "path": path}
            if details is not None:
                diagnostic["details"] = details
            corrected = {**observation, "correction": {
                "schema_version": 4, "binding": {"correction_ordinal": 1},
                "diagnostics": [diagnostic]}}
            text = render_prompt(corrected, example).decode("utf-8")
            self.assertIn("This is an envelope refusal", text)
            self.assertNotIn("The fault is the envelope's own binding", text)
            if details is not None:
                self.assertIn("unexpected: clauses, dropped", text)

    def test_a_content_correction_is_not_introduced_as_an_envelope_refusal(self):
        """Only an envelope refusal is decided before the clauses are read.

        A lexical error, a dead resubmission and a drop conflict are content
        refusals; announcing each of them as a binding refusal misdescribes the
        correction the agent has to act on. Each carries its own one-line gloss,
        and `dead_clause_rejected` is named rather than left to be inferred.
        """
        observation, example = recorded()
        for code, expected in (
                ("clause_lexical_error", "`⊇` (write `(B ⊆ A)`)"),
                ("clause_syntax_error", "parenthesis around a prefix"),
                ("clause_schema_error", "the wrong arity"),
                ("unauthorized_drop", "IDENTITIES AND DROP REFERENCES"),
                ("dead_clause_rejected", "permanently dead"),
                ("drop_submission_conflict", "drop only what you want gone")):
            corrected = {**observation, "correction": {
                "schema_version": 4, "binding": {"correction_ordinal": 1},
                "diagnostics": [{"code": code, "message": "refused.",
                                 "item_index": 0, "path": None}]}}
            text = render_prompt(corrected, example).decode("utf-8")
            self.assertIn(code, text)
            self.assertIn(expected, text)
            self.assertIn("item_index: 0", text)
            self.assertNotIn("This is an envelope refusal", text)

    def test_the_envelope_names_the_response_example_as_the_only_binding(self):
        prompt, _ = render_module.render(EXAMPLE0001)
        text = prompt.decode("utf-8")
        self.assertIn("Copy the `binding` object from the RESPONSE EXAMPLE below exactly", text)
        self.assertIn("It is the only", text)
        self.assertIn("binding you are shown", text)
        self.assertNotIn("inside the observation", text)

    def test_a_clause_without_readable_text_says_so(self):
        observation, example = recorded()
        feedback = {**observation["feedback"],
                    "core": [{"clause": {"clause_id": 4, "canonical_source": None,
                                         "display": None},
                              "source": "symbolic", "level": 0}]}
        prompt = render_prompt({**observation, "feedback": feedback}, example)
        self.assertIn("no readable text for this clause", prompt.decode("utf-8"))

    def test_clause_spelling_covers_every_canonical_key_form(self):
        """Exactly the spellings the repository's own admission guards pin.

        `Whiel/Synthesis/Tests/FrameworkIIFixedAmbientAdmission.lean` guards
        `op_szR`, `oa_zT`, `yp_zR` and `of_z1`; the key encoding is
        `Whiel/Concrete/WhielNames/Notation.lean`. Nothing here is guessed, so
        the table never sends the agent to `validate_clauses` for a name the
        repository proves.
        """
        for key, spelling, display in (
                ("o:p::E", "op_zE", "E"),
                ("y:p::T", "yp_zT", "T∞"),
                ("o:a::T", "oa_zT", "T_aux"),
                ("y:a::T", "ya_zT", "T_aux∞"),
                ("o:p:s:R", "op_szR", "R_1"),
                ("o:a:ss:R", "oa_sszR", "R_aux_2"),
                ("o:f::1", "of_z1", "flag_1_0"),
                ("y:f:s:12", "yf_sz12", "flag_12_1∞")):
            self.assertEqual(clause_spelling(key), spelling, key)
            self.assertEqual(prompt_module._display_name(key), display, key)
        for key in ("y:f::ss3", "o:p::E1", "o:x::E", "y:p:t:T", "nonsense", "o:f::01"):
            self.assertIsNone(clause_spelling(key), key)
            self.assertEqual(prompt_module._display_name(key), key, key)

    def test_no_asset_prints_a_benchmark_clause_in_any_spelling(self):
        """The explanation must not hand the proposer a corpus answer.

        A rendered benchmark clause is one the model can copy without
        reasoning, which makes a certification of that benchmark evidence of
        nothing. The manual's syntax examples are over an invented schema, and
        the skill library, though absent from the prompt unless enabled, is
        held to the same exact-match rule.

        Scope: every `Core.json` under `Benchmark/` and `Legacy/Benchmark/`
        (canonical clause sources), and every `qfAssert![...]` block in the
        certificates under `Benchmark/*/Certificate/` (the same clauses in
        their *display* spelling, which a canonical-source comparison would
        miss). Whitespace is normalized on both sides, so re-spacing a clause
        does not get it past this test. The manual is also checked with the
        relation names normalized away, so a corpus clause cannot enter it by
        renaming its relations; that check is limited to shapes with at least
        four relation occurrences, since smaller shapes (a containment, a
        composition inside a relation) are the grammar itself and recur across
        the corpus.
        """
        root = Path(__file__).resolve().parents[2]
        def squeeze(text):
            return "".join(text.split())
        sources = [row["source"]
                   for pattern in ("Benchmark/*/Core.json", "Legacy/Benchmark/**/Core.json")
                   for core in sorted(root.glob(pattern))
                   for row in json.loads(core.read_text(encoding="utf-8"))["rows"]]
        displays = [match.group(1)
                    for certificate in sorted(root.glob("Benchmark/*/Certificate/**/*.lean"))
                    for match in re.finditer(r"qfAssert!\[\s*(.*?)\s*\]\n",
                                             certificate.read_text(encoding="utf-8"),
                                             re.DOTALL)]
        self.assertTrue(sources, "no benchmark Core rows found to check against")
        self.assertTrue(displays, "no certificate clause displays found to check against")
        explanation = squeeze("\n".join(asset_text(name) for name in ASSET_ORDER))
        library = squeeze("\n".join(path.read_text(encoding="utf-8") for path in
                                    sorted((root / "agent_houdini" / "skills" / "v1").glob("*.md"))))
        for clause in sources + displays:
            self.assertNotIn(squeeze(clause), explanation, clause)
            self.assertNotIn(squeeze(clause), library, clause)
        # Renaming check for the manual: relation tokens numbered by first use.
        token = re.compile(r"\b[oy][paf]_s*z[A-Za-z0-9]+\b")
        def shape(clause):
            names = {}
            def rename(match):
                return names.setdefault(match.group(0), f"R{len(names) + 1}")
            renamed = token.sub(rename, clause)
            return squeeze(renamed), len(token.findall(clause))
        corpus = {shape(clause)[0] for clause in sources if shape(clause)[1] >= 4}
        printed = [line.strip() for name in ASSET_ORDER
                   for line in asset_text(name).split("\n")
                   if line.strip().startswith("(") and "_z" in line]
        for clause in printed:
            renamed, count = shape(clause)
            if count >= 4:
                self.assertNotIn(renamed, corpus, clause)

    def test_assets_exist_and_lose_only_their_provenance_comment(self):
        for name in ASSET_ORDER:
            text = asset_text(name)
            self.assertTrue(text.startswith("#"), name)
            self.assertNotIn("<!--", text)
            self.assertNotIn("Framework II", text)
            self.assertNotIn("Framework-II", text)

    def test_missing_example_or_observation_is_an_error(self):
        with self.assertRaisesRegex(ValueError, "push lacks response binding"):
            render_prompt({}, b"")
        with self.assertRaisesRegex(ValueError, "expected an observation object"):
            render_prompt([], b"{}")


class RenderToolTests(unittest.TestCase):
    def test_a_directory_is_searched_for_a_recorded_observation(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            (root / "deep").mkdir()
            (root / "deep" / "other.json").write_bytes(b'{"unrelated":true}')
            (root / "deep" / "record.json").write_bytes(EXAMPLE0001.read_bytes())
            prompt, source = render_module.render(root)
            self.assertEqual(source, root / "deep" / "record.json")
            self.assertEqual(prompt, (FIXTURES / "example0001_prompt.txt").read_bytes())

    def test_a_bare_observation_renders_with_a_marked_placeholder_example(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "observation.json"
            path.write_bytes(encode(recorded()[0]))
            prompt, _ = render_module.render(path)
            self.assertIn(b'"request_digest":"' + b"0" * 64, prompt)

    def test_an_unusable_path_is_refused(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "empty.json"
            path.write_bytes(b"{}")
            with self.assertRaises(render_module.RenderError):
                render_module.render(path)
            with self.assertRaises(render_module.RenderError):
                render_module.render(Path(name) / "absent")

    def test_the_entry_point_prints_the_rendered_prompt(self):
        out, notes = io.BytesIO(), io.StringIO()
        self.assertEqual(render_module.main([str(EXAMPLE0001)], out=out, notes=notes), 0)
        self.assertEqual(out.getvalue(), (FIXTURES / "example0001_prompt.txt").read_bytes())
        self.assertIn(f"{len(out.getvalue())} bytes", notes.getvalue())
        self.assertEqual(render_module.main(["--help"], notes=notes), 0)
        self.assertEqual(render_module.main(["a", "b"], notes=notes), 2)

    def test_the_package_entry_point_routes_render_prompt(self):
        from agent_houdini.launcher import main

        self.assertEqual(main(["--help"]), 0)
        self.assertEqual(main(["render-prompt", "a", "b"]), 2)


if __name__ == "__main__":
    unittest.main()
