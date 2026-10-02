#!/usr/bin/env python3
"""Public API peer replaying a repository record; no engine or C imports.

One request per input, answered with the answer the repository already holds
for it — `Benchmark/<ID>/Core.json` as `candidate_clauses`, or
`Benchmark/<ID>/Counterexample.json` as `candidate_counterexample`. Nothing
here claims the answer is right: B's own verifier does all the checking, so a
campaign driven by this peer exercises the accepted path of both verdicts
without a model. An input with neither record is declined at once.
"""

import json
import os
import socket
import struct
import sys

WIRE = 3
CORE_KIND = "whiel_framework_ii_core_rows"
COUNTEREXAMPLE_KIND = "whiel_framework_ii_counterexample"
ATTACHED = {"request": ("observation_bytes", "response_example_bytes")}


def encoded(value):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode()


repository = sys.argv[1]
token = os.environ["WHIEL_PROPOSER_TOKEN"]
stream = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
stream.settimeout(300)
sent = received = 0
request_id = None


def send(kind, attachments=(), **fields):
    global sent
    header = encoded(dict(wire_version=WIRE, endpoint_token=token, sequence=sent,
                          request_id=request_id, operation=dict(kind=kind, **fields)))
    assert 0 < len(header) <= 16384
    stream.sendall(struct.pack(">I", len(header)) + header + b"".join(attachments))
    sent += 1


def exact(length):
    assert 0 <= length <= 64 * 1024 * 1024
    value = bytearray()
    while len(value) < length:
        part = stream.recv(min(length - len(value), 65536))
        if not part:
            raise EOFError("endpoint closed")
        value.extend(part)
    return bytes(value)


def receive(expected):
    global received
    size, = struct.unpack(">I", exact(4))
    assert 0 < size <= 16384
    frame = json.loads(exact(size))
    assert frame["wire_version"] == WIRE and frame["endpoint_token"] == token
    assert frame["sequence"] == received
    received += 1
    operation = frame["operation"]
    assert operation["kind"] in expected, operation
    return frame, [exact(operation[key]) for key in ATTACHED.get(operation["kind"], ())]


def answer(identity):
    """The recorded response body for one input, or None when there is none."""
    assert identity and "/" not in identity and identity not in (".", "..")
    directory = os.path.join(repository, "Benchmark", identity)
    core = os.path.join(directory, "Core.json")
    counterexample = os.path.join(directory, "Counterexample.json")
    if os.path.isfile(core):
        with open(core, encoding="utf-8") as document:
            record = json.load(document)
        assert record["kind"] == CORE_KIND, identity
        rows = sorted(record["rows"], key=lambda row: row["level"])
        return "candidate_clauses", [row["source"] for row in rows]
    if os.path.isfile(counterexample):
        with open(counterexample, encoding="utf-8") as document:
            record = json.load(document)
        assert record["kind"] == COUNTEREXAMPLE_KIND, identity
        relations = record["instance"]["relations"]
        return "candidate_counterexample", {
            "relations": [{"name": relation["name"], "rows": relation["rows"]}
                          for relation in relations]}
    return None


stream.connect(os.environ["WHIEL_PROPOSER_SOCKET"])
send("hello", capabilities=dict(version="3.0.0", supported_operations=[],
                                required_operations=[]))
receive({"ready"})
recorded = None
while True:
    frame, attachments = receive({"request", "shutdown", "cancel"})
    kind = frame["operation"]["kind"]
    if kind == "shutdown":
        send("closed")
        break
    request_id = frame["request_id"]
    if kind == "cancel":
        send("complete", outcome="failure")
        receive({"request_closed"})
        request_id = None
        continue
    observation, example = (json.loads(part) for part in attachments)
    identity = observation["feedback"]["presentation"]["task"]["canonical_id"]
    if recorded is None:
        recorded = answer(identity)
    # One replayed answer settles the input, so a second request means the
    # recorded answer did not stand: decline rather than resubmit it.
    if recorded is None or frame["request_id"] > 1:
        send("complete", outcome="source_exhausted")
        receive({"request_closed"})
        break
    body = dict(kind=recorded[0], schema_version=example["schema_version"],
                binding=example["binding"])
    if recorded[0] == "candidate_clauses":
        body["clauses"], body["dropped"] = list(recorded[1]), []
    else:
        body["input"] = recorded[1]
    payload = encoded(body)
    send("submit", (payload,), bytes=len(payload))
    submitted, _ = receive({"submitted", "rejected", "cancel"})
    send("complete",
         outcome="response" if submitted["operation"]["kind"] == "submitted" else "failure")
    receive({"request_closed"})
    request_id = None
