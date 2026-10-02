# Author: Fangzhu Shen
"""Check that the synthetic native acceptance fixture uses only public inputs."""
import json
from pathlib import Path
import unittest
from copy import deepcopy

from agent_houdini.tests.fixtures.endpoint_acceptance import (
    CLAUSES, inspect_and_propose, prompt_objects,
)


class EndpointAcceptanceFixtureTests(unittest.TestCase):
    def documents(self, correction=None):
        return ({"feedback": {"presentation": {"ambient_schema": {"relations": [{"key": "R"}]}}},
                 "correction": correction},
                {"schema_version": 4, "kind": "candidate_clauses", "binding": {
                    "request_digest": "1" * 64}, "clauses": [], "dropped": []})

    def test_the_golden_rendered_prompt_still_yields_both_public_documents(self):
        """C's rendering may change; the fixture must keep finding B's documents."""
        fixtures = Path(__file__).resolve().parents[1] / "fixtures"
        prompt = (fixtures / "example0001_prompt.txt").read_text(encoding="utf-8")
        observation, response = prompt_objects(prompt)
        self.assertIsNone(observation["correction"])
        self.assertEqual(observation["feedback"]["presentation"]["ambient_schema"]["relations"],
                         [{"key": key, "arity": 2} for key in
                          ("o:p::E", "o:p::S", "o:p::T", "y:p::S", "y:p::T")])
        self.assertEqual([observation["feedback"][name] for name in ("core", "pending", "last_round")],
                         [[], [], []])
        self.assertEqual(response["schema_version"], 4)
        self.assertEqual(response["clauses"], [])
        self.assertEqual(len(response["binding"]), 8)
        # A populated later push: every listed clause carries its identity from the tail.
        later, _ = prompt_objects((fixtures / "example2004_prompt.txt").read_text(encoding="utf-8"))
        feedback = later["feedback"]
        self.assertEqual([item["clause"]["clause_id"] for item in feedback["core"]], [0])
        self.assertEqual([item["clause"]["clause_id"] for item in feedback["pending"]], [1, 2, 3, 4, 5])
        self.assertEqual([item["clause"]["clause_id"] for item in feedback["last_round"]], [1, 2, 3, 4, 5])
        for item in feedback["pending"]:
            self.assertEqual(set(item["clause"]), {"clause_id", "record_digest", "formula_digest"})
            self.assertEqual(len(item["clause"]["record_digest"]), 64)
        recorded = json.loads((fixtures / "example2004_consultation.json").read_text(encoding="utf-8"))
        self.assertEqual(feedback["presentation"]["ambient_schema"]["relations"],
                         [{"key": relation["key"], "arity": relation["arity"]} for relation in
                          recorded["observation"]["feedback"]["presentation"]["ambient_schema"]["relations"]])

    def test_a_rendered_correction_is_read_with_its_codes(self):
        prompt = ("# Correction on your previous response\n\nYour previous response was refused.\n\n"
                  "    drop_target_not_eligible: refused.\n        item_index: 0\n\n"
                  "# Task Example0001 — consultation 2\n\n# Relations\n\n"
                  "    push key      displayed     in a clause    arity   prophecy pairing\n"
                  "    o:p::E        E             op_zE          2       no prophecy copy\n"
                  "    o:f::1        flag_1_0      (ask validate_clauses) 0       no prophecy copy\n\n"
                  "# Current Core (0 clauses)\n\nEmpty.\n\nRESPONSE EXAMPLE:\n"
                  '{"schema_version":4,"kind":"candidate_clauses","binding":{"a":"b"},"clauses":[],"dropped":[]}\n')
        observation, response = prompt_objects(prompt)
        self.assertEqual(observation["correction"], {"diagnostics": [
            {"code": "drop_target_not_eligible", "message": "refused."}]})
        self.assertEqual(observation["feedback"]["presentation"]["ambient_schema"]["relations"],
                         [{"key": "o:p::E", "arity": 2}, {"key": "o:f::1", "arity": 0}])
        self.assertEqual(response["binding"], {"a": "b"})

    def test_prompt_parser_handles_changed_prose_and_document_order(self):
        observation, response = self.documents()
        for values in ((observation, response), (response, observation)):
            prompt = "arbitrary {bad text\n" + "\nchanged prose\n".join(map(json.dumps, values))
            self.assertEqual(prompt_objects(prompt), (observation, response))
        with self.assertRaisesRegex(ValueError, "missing public"):
            prompt_objects(json.dumps(response))

    def test_wrong_binding_then_correction_preserve_opaque_payload_and_public_queries(self):
        for correction in (None, {"reason": "binding"}):
            observation, response = self.documents(correction)
            events, queries, payloads = [], [], []
            def rpc(method, params):
                self.assertEqual(method, "tools/call")
                name, args = params["name"], params["arguments"]
                queries.append((name, args))
                if name == "submit":
                    payloads.append(args["payload"])
                    return {"result": {"isError": False}}
                value = {"tool": name, "state_revision": 7, "result": {}}
                if name == "validate_clauses":
                    value["result"] = {"results": [{"admitted": True} for _ in CLAUSES]}
                elif name == "evaluate_clauses":
                    value["result"] = {"instances": [{"kind": "supplied", "source_index": 0}],
                                       "skipped": [], "results": [{"admitted": True, "holds": [True]} for _ in CLAUSES]}
                return {"result": {"content": [{"text": json.dumps(value)}]}}
            inspect_and_propose(rpc, observation, response, [{"name": "ledger"}],
                                lambda kind, **fields: events.append((kind, fields)))
            self.assertEqual([name for name, _ in queries],
                             ["ledger", "validate_clauses", "evaluate_clauses", "ledger", "submit"])
            self.assertTrue(payloads[0].startswith(" \n") and payloads[0].endswith("\n "))
            self.assertEqual(json.loads(payloads[0])["binding"]["request_digest"],
                             ("0" if correction is None else "1") * 64)
            self.assertEqual(events[-1][1]["correction_seen"], correction is not None)

    def test_changed_ledger_is_a_failed_acceptance_not_a_silent_pass(self):
        observation, response = self.documents()
        count = 0
        def rpc(method, params):
            nonlocal count
            name = params["name"]
            value = {"tool": name, "result": {}}
            if name == "ledger":
                count += 1
                value["state_revision"] = count
            elif name == "validate_clauses":
                value["result"] = {"results": [{"admitted": True} for _ in CLAUSES]}
            elif name == "evaluate_clauses":
                value["result"] = {"instances": [{"kind": "supplied", "source_index": 0}], "skipped": [],
                                   "results": [{"admitted": True, "holds": [True]} for _ in CLAUSES]}
            else:
                self.fail("must not submit after mutation")
            return {"result": {"content": [{"text": json.dumps(value)}]}}
        with self.assertRaisesRegex(ValueError, "changed the ledger"):
            inspect_and_propose(rpc, observation, deepcopy(response), [{"name": "ledger"}], lambda *a, **k: None)
