# Author: Fangzhu Shen
"""Public-data-only model/historical native acceptance scenarios."""

from copy import deepcopy
import json
import unittest

from agent_houdini.tests.fixtures.endpoint_acceptance import (
    CLAUSES, REFUTABLE, inspect_full_models, inspect_historical,
)


class PublicCalls:
    def __init__(self, identity=417, *, retained=False, historical=False):
        self.reference = {"clause_id": identity, "record_digest": "2" * 64, "formula_digest": "3" * 64}
        self.attempt = identity + 23
        self.retained, self.historical = retained, historical
        self.calls, self.submitted, self.events = [], [], []
        self.retained_holds = False
        self.row = {"kind": "attempt", "clause": self.reference,
                    "result": {"attempt_id": self.attempt, "outcome": {"kind": "refuted"}}}

    def record(self, kind, **fields):
        self.events.append((kind, fields))

    def rpc(self, method, params):
        assert method == "tools/call"
        name, args = params["name"], params["arguments"]
        self.calls.append((name, deepcopy(args)))
        if name == "submit":
            self.submitted.append(json.loads(args["payload"]))
            return {"result": {"isError": False}}
        if name == "ledger":
            if self.historical and not args:
                result = {"items": [{"kind": "attempt", "result": {"outcome": {"kind": "proved"}}}],
                          "metadata": {"continuation": "19"}}
            else:
                assert not args or args == {"cursor": "19"}
                result = {"items": [self.row] if self.retained or self.historical else [],
                          "metadata": {"continuation": None}}
        elif name == "validate_clauses":
            result = {"results": [{"admitted": True} for _ in args["clauses"]]}
        elif name == "history":
            assert args == {"clause": self.reference}
            result = {"clause": self.reference, "current_level": None,
                      "status": {"kind": "dead", "cause": "refuted"}, "attempts": [self.row]}
        elif name == "strongest_refutations":
            assert args == {"clause": self.reference}
            result = {"refutations": [{"attempt": self.attempt}]}
        elif name == "countermodel":
            assert args == {"attempt": self.attempt}
            result = {"clause": self.reference, "attempt": self.attempt, "model": {"relations": [{"name": "R"}]}}
        elif name == "evaluate_clauses":
            retained = args["instances"][0]["kind"] == "retained"
            if retained:
                assert args["instances"][0]["attempt"] == self.attempt
            result = {"instances": [{"kind": "retained", "source_index": 0, "attempt": self.attempt}
                                    if retained else {"kind": "supplied", "source_index": 0}],
                      "skipped": [], "results": [{"admitted": True,
                          "holds": [self.retained_holds if retained else True]} for _ in args["clauses"]]}
        else:
            raise AssertionError(name)
        return {"result": {"content": [{"text": json.dumps({"tool": name, "state_revision": 8, "result": result})}]}}


def documents(correction=None):
    observation = {"feedback": {"core": [], "pending": [], "last_round": [],
        "presentation": {"ambient_schema": {"relations": [{"key": "R"}]}}}, "correction": correction}
    response = {"schema_version": 4, "kind": "candidate_clauses", "binding": {
        "request_digest": "1" * 64, "consultation_digest": "4" * 64}, "clauses": [], "dropped": []}
    return observation, response


class ModelAcceptanceTests(unittest.TestCase):
    def test_full_flow_requests_refutation_then_discovers_opaque_references(self):
        for correction, retained, expected in [(None, False, CLAUSES), ({}, False, [REFUTABLE]), (None, True, CLAUSES)]:
            calls = PublicCalls(936, retained=retained)
            observation, response = documents(correction)
            inspect_full_models(calls.rpc, observation, response, [], calls.record)
            proposal = calls.submitted[0]
            self.assertEqual(proposal["clauses"], expected)
            self.assertEqual(proposal["binding"]["request_digest"], ("0" if correction is None and not retained else "1") * 64)
            if retained:
                self.assertEqual({name for name, _ in calls.calls}, {
                    "ledger", "history", "strongest_refutations", "countermodel", "validate_clauses", "evaluate_clauses", "submit"})

    def test_model_that_does_not_refute_never_yields_success(self):
        calls = PublicCalls(retained=True)
        calls.retained_holds = True
        with self.assertRaisesRegex(ValueError, "does not refute"):
            inspect_full_models(calls.rpc, *documents(), [], calls.record)
        self.assertEqual(calls.submitted, [])

    def test_historical_discovers_later_page_and_submits_no_read_derived_authority(self):
        for identity in (43, 981):
            calls = PublicCalls(identity, historical=True)
            inspect_historical(calls.rpc, *documents(), [], calls.record)
            self.assertEqual(calls.calls[:2], [("ledger", {}), ("ledger", {"cursor": "19"})])
            self.assertEqual(calls.submitted[0]["dropped"], [{"clause": calls.reference,
                "consultation_digest": "4" * 64, "authorization_digest": "0" * 64}])
            correction = {"diagnostics": [{"code": "drop_target_not_eligible"}]}
            inspect_historical(calls.rpc, *documents(correction), [], calls.record)
            self.assertEqual(calls.submitted[1]["clauses"], [])
            self.assertEqual(calls.submitted[1]["dropped"], [])

    def test_wrong_historical_correction_is_not_silently_accepted(self):
        calls = PublicCalls(historical=True)
        with self.assertRaisesRegex(ValueError, "wrong drop correction"):
            inspect_historical(calls.rpc, *documents({"diagnostics": [{"code": "other"}]}), [], calls.record)
        self.assertEqual(calls.submitted, [])
