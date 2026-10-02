#!/usr/bin/env python3
"""Deterministic public-API fixture; no Whiel or AgentHoudini imports.

The two successful clauses are fixed Example0001 test inputs, not read from
certificate artifacts. B independently verifies and certifies their proposal.
This fixture is deliberately small; production client conformance is tested
separately. Its optional diagnostic trace is not semantic acceptance authority.
"""

import argparse
import json
import os
import socket
import struct


QUERIES = ["countermodel", "strongest_refutations", "history", "ledger",
           "validate_clauses", "evaluate_clauses"]
CLAUSES = ["(op_zS = (op_zE ∪ π[0,3] (σ[#1 = #2] ((op_zE × op_zT)))))",
           "(π[0,3] (σ[#1 = #2] ((op_zT × yp_zT))) ⊆ yp_zT)"]
REFUTABLE = "(op_zE = ∅[2])"
ATTACHMENTS = {"request": ("observation_bytes", "response_example_bytes"),
               "query_result": ("result_bytes",)}
MAX_PACKET = 64 * 1024 * 1024


def encoded(value):
    return json.dumps(value, ensure_ascii=False, allow_nan=False,
                      separators=(",", ":")).encode("utf-8")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact(stream, length):
    require(type(length) is int and 0 <= length <= MAX_PACKET, "invalid length")
    result = bytearray()
    while len(result) < length:
        part = stream.recv(min(length - len(result), 65536))
        require(part, "truncated packet")
        result.extend(part)
    return bytes(result)


class Endpoint:
    def __init__(self, trace):
        self.trace = trace
        self.token = os.environ["WHIEL_PROPOSER_TOKEN"]
        self.socket = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.socket.settimeout(120)
        self.socket.connect(os.environ["WHIEL_PROPOSER_SOCKET"])
        self.sent = self.received = 0
        self.request_id = None
        self.query_id = 0

    def log(self, kind, **fields):
        with open(self.trace, "ab") as output:
            output.write(encoded({"kind": kind, "pid": os.getpid(), **fields}) + b"\n")

    def send(self, kind, attachments=(), **fields):
        header = encoded({"wire_version": 3, "endpoint_token": self.token,
                          "sequence": self.sent, "request_id": self.request_id,
                          "operation": {"kind": kind, **fields}})
        require(len(header) <= 16384, "oversized header")
        require(4 + len(header) + sum(map(len, attachments)) <= MAX_PACKET,
                "oversized packet")
        self.socket.sendall(struct.pack(">I", len(header)) + header + b"".join(attachments))
        self.sent += 1

    def receive(self, expected):
        size, = struct.unpack(">I", exact(self.socket, 4))
        require(0 < size <= 16384, "oversized incoming header")
        frame = json.loads(exact(self.socket, size))
        require(set(frame) == {"wire_version", "endpoint_token", "sequence",
                              "request_id", "operation"}, "unexpected envelope")
        require(frame["wire_version"] == 3 and frame["endpoint_token"] == self.token,
                "wrong API identity")
        require(frame["sequence"] == self.received, "wrong incoming sequence")
        self.received += 1
        operation = frame["operation"]
        require(operation["kind"] in expected, "unexpected operation: " + str(operation))
        lengths = [operation[key] for key in ATTACHMENTS.get(operation["kind"], ())]
        require(4 + size + sum(lengths) <= MAX_PACKET, "oversized attachments")
        return frame, [exact(self.socket, length) for length in lengths]

    def query(self, name, arguments):
        self.query_id += 1
        argument_bytes = encoded(arguments)
        self.send("query", (argument_bytes,), query_id=self.query_id,
                  name=name, args_bytes=len(argument_bytes))
        frame, attachments = self.receive({"query_result"})
        require(frame["request_id"] == self.request_id, "wrong reply request")
        require(frame["operation"]["query_id"] == self.query_id, "wrong reply query")
        reply = json.loads(attachments[0])
        require(reply["tool"] == name and "result" in reply, "query failed: " + str(reply))
        self.log("query", request_id=self.request_id, name=name,
                 arguments=arguments, reply=reply)
        return reply

    def submit(self, response):
        payload = encoded(response)
        self.send("submit", (payload,), bytes=len(payload))
        frame, _ = self.receive({"submitted"})
        require(frame["request_id"] == self.request_id, "wrong submission receipt")
        self.log("submission", request_id=self.request_id, response=response)
        self.complete("response")

    def complete(self, outcome):
        self.send("complete", outcome=outcome)
        frame, _ = self.receive({"request_closed"})
        require(frame["request_id"] == self.request_id, "wrong closure receipt")
        self.request_id = None


def inspect_queries(endpoint, observation):
    before = endpoint.query("ledger", {})
    validation = endpoint.query("validate_clauses", {"clauses": CLAUSES})["result"]
    require(len(validation["results"]) == len(CLAUSES)
            and all(row.get("admitted") is True for row in validation["results"]),
            "canonical clauses were not admitted by semantic validation")
    schema = observation["feedback"]["presentation"]["ambient_schema"]
    instance = {"carrier_keys": ["num:0"], "relations": [
        {"name": relation["key"], "rows": []} for relation in schema["relations"]]}
    supplied = endpoint.query("evaluate_clauses", {"clauses": CLAUSES,
                   "instances": [{"kind": "supplied", "instance": instance}]})["result"]
    require(supplied["instances"] == [{"kind": "supplied", "source_index": 0}]
            and supplied["skipped"] == []
            and len(supplied["results"]) == len(CLAUSES)
            and all(row.get("admitted") is True and row.get("holds") == [True]
                    for row in supplied["results"]),
            "supplied-instance evaluation did not return expected clause truth")
    page = before["result"]
    refs = []
    while True:
        for row in page["items"]:
            reference = row.get("clause", row.get("target"))
            if reference not in refs:
                refs.append(reference)
        cursor = page["metadata"]["continuation"]
        if cursor is None:
            break
        page = endpoint.query("ledger", {"cursor": cursor})["result"]
    refuted = False
    for reference in refs:
        history = endpoint.query("history", {"clause": reference})["result"]
        endpoint.query("strongest_refutations", {"clause": reference})
        for row in history["attempts"]:
            result = row["result"]
            if result["outcome"]["kind"] == "refuted":
                attempt = result["attempt_id"]
                require(attempt is not None, "refutation missing exposed attempt")
                countermodel = endpoint.query("countermodel", {"attempt": attempt})["result"]
                require(countermodel["attempt"] == attempt and "model" in countermodel,
                        "refuted check did not expose a retained countermodel")
                retained = endpoint.query("evaluate_clauses", {"clauses": [REFUTABLE],
                               "instances": [{"kind": "retained", "attempt": attempt}]})["result"]
                require(retained["instances"] == [{"kind": "retained", "attempt": attempt,
                                                   "source_index": 0}]
                        and retained["skipped"] == []
                        and len(retained["results"]) == 1
                        and retained["results"][0].get("admitted") is True
                        and len(retained["results"][0].get("holds", [])) == 1
                        and type(retained["results"][0]["holds"][0]) is bool,
                        "retained-instance evaluation was skipped or not admitted")
                refuted = True
    after = endpoint.query("ledger", {})
    require(before == after, "read-only calls changed the runtime ledger")
    endpoint.log("read_only_ledger", request_id=endpoint.request_id,
                 state_revision=before["state_revision"], refuted=refuted)
    return refuted


def historical_queries(endpoint, observation):
    arguments = {}
    cursors = set()
    for pages in range(1, 129):
        page = endpoint.query("ledger", arguments)["result"]
        require(len(page["items"]) == 1, "historical fixture must require pagination")
        row = page["items"][0]
        if row["kind"] == "attempt" and row["result"]["outcome"]["kind"] == "refuted":
            require(pages > 1, "old refutation must not be on the first page")
            break
        cursor = page["metadata"]["continuation"]
        require(isinstance(cursor, str) and cursor not in cursors,
                "historical cursor must advance")
        cursors.add(cursor)
        arguments = {"cursor": cursor}
    else:
        raise ValueError("historical pagination exceeded fixture bound")
    clause, attempt = row["clause"], row["result"]["attempt_id"]
    require(type(attempt) is int, "missing exposed historical attempt")
    for name in ("core", "pending", "last_round"):
        require(all(entry["clause"] != clause for entry in observation["feedback"][name]),
                "historical clause is in the initial displayed lists")
    history = endpoint.query("history", {"clause": clause})["result"]
    require(history["clause"] == clause and history["status"]["kind"] == "dead"
            and history["status"]["cause"] == "refuted", "historical clause is not dead")
    model = endpoint.query("countermodel", {"attempt": attempt})["result"]
    require(model["attempt"] == attempt and model["clause"] == clause
            and bool(model["model"]["relations"]), "historical model was not retained")
    evaluated = endpoint.query("evaluate_clauses", {"clauses": [REFUTABLE],
                  "instances": [{"kind": "retained", "attempt": attempt}]})["result"]
    require(evaluated["instances"] == [{"kind": "retained", "source_index": 0,
                                        "attempt": attempt}]
            and evaluated["skipped"] == [] and evaluated["results"][0]["admitted"] is True
            and evaluated["results"][0]["holds"] == [False],
            "historical model did not falsify the admitted clause")
    return clause


def run(trace, mode="full"):
    require(mode in {"full", "certificate", "historical", "admission",
                     "no_response", "failure", "source_exhausted", "endpoint_exit", "api_flood"},
            "unknown fixture mode")
    endpoint = Endpoint(trace)
    endpoint.send("hello", capabilities={"version": "3.0.0",
                  "supported_operations": QUERIES, "required_operations": QUERIES})
    frame, _ = endpoint.receive({"ready"})
    require(frame["request_id"] is None, "scoped handshake")
    require(set(frame["operation"]["api"]["operations"]) == set(QUERIES),
            "missing required API query")
    previous = 0
    correction_seen = refutation_seen = False
    try:
        while True:
            frame, attachments = endpoint.receive({"request", "shutdown"})
            if frame["operation"]["kind"] == "shutdown":
                require(frame["request_id"] is None, "scoped shutdown")
                endpoint.send("closed")
                endpoint.log("closed", mode=mode, correction_seen=correction_seen,
                             refutation_seen=refutation_seen)
                return
            request_id = frame["request_id"]
            require(type(request_id) is int and request_id == previous + 1,
                    "request was not fresh")
            previous = request_id
            require(request_id <= 5, "fixture did not converge")
            endpoint.request_id, endpoint.query_id = request_id, 0
            observation, response = map(json.loads, attachments)
            endpoint.log("observation", request_id=request_id, observation=observation)
            correction_seen |= observation["correction"] is not None
            if mode == "endpoint_exit":
                raise SystemExit(17)
            if mode in {"no_response", "failure", "source_exhausted"}:
                print("ordinary endpoint prose is not a proposal", flush=True)
                endpoint.complete(mode)
                continue
            if mode == "api_flood":
                for _ in range(128):
                    endpoint.query("ledger", {})
                raise ValueError("bounded query flood did not exhaust configured API budget")
            if mode == "admission":
                require(request_id == 1, "admission fixture needs exactly one request")
                endpoint.query("ledger", {})
                response["clauses"] = CLAUSES
                endpoint.submit(response)
                continue
            if mode == "historical":
                if request_id == 1:
                    clause = historical_queries(endpoint, observation)
                    response["dropped"] = [{"clause": clause,
                        "consultation_digest": response["binding"]["consultation_digest"],
                        "authorization_digest": "0" * 64}]
                else:
                    require(request_id == 2 and correction_seen,
                            "historical drop must receive exactly one correction")
                    require(any(item["code"] == "drop_target_not_eligible"
                                for item in observation["correction"]["diagnostics"]),
                            "historical read unexpectedly granted drop authority")
                    require(observation["binding"]["validation_ordinal"] == 1,
                            "historical correction must advance validation ordinal")
                endpoint.submit(response)
                continue
            refutation_seen |= inspect_queries(endpoint, observation)
            if request_id == 1:
                # Well-framed, syntactically valid proposal with a false binding.
                response["binding"]["request_digest"] = "0" * 64
                response["clauses"] = CLAUSES
            elif request_id == 2 and mode == "full":
                require(correction_seen, "wrong binding did not receive correction")
                response["clauses"] = [REFUTABLE]
            else:
                require(correction_seen, "wrong binding did not receive correction")
                if mode == "full":
                    require(refutation_seen, "refutable clause produced no accessible refutation")
                response["clauses"] = CLAUSES
            endpoint.submit(response)
    except BaseException as error:
        endpoint.log("fixture_failure", request_id=endpoint.request_id, error=repr(error))
        raise
    finally:
        endpoint.socket.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace", required=True)
    parser.add_argument("--mode", choices=("full", "certificate", "historical", "admission",
                                               "no_response", "failure", "source_exhausted", "endpoint_exit", "api_flood"), default="full")
    options = parser.parse_args()
    run(options.trace, options.mode)
