"""Synthetic provider-neutral wire peer. Never invokes a model or engine tools."""
import json
import os
from pathlib import Path
import socket
import struct
import subprocess
import sys
import time

mode = sys.argv[1]
log = Path(sys.argv[2]) if len(sys.argv) > 2 else None
sequence = 0
expected = 0
token = os.environ["WHIEL_PROPOSER_TOKEN"]
restart_fixture = mode in {"blocked_request", "blocked_reply"}
if log:
    with log.open("a" if restart_fixture else "w") as output:
        output.write(json.dumps({"event": "start", "pid": os.getpid(), "token": token}) + "\n")
if restart_fixture:
    assert log is not None
    try:
        with log.with_suffix(".once").open("x"):
            pass
    except FileExistsError:
        mode = "normal"
if mode == "startup_hang":
    time.sleep(60)
    raise SystemExit(1)
peer = socket.socket(socket.AF_UNIX)
peer.connect(os.environ["WHIEL_PROPOSER_SOCKET"])


def record(**values):
    if log:
        with log.open("a") as output:
            output.write(json.dumps(values) + "\n")


def exact(size):
    result = b""
    while len(result) < size:
        part = peer.recv(size - len(result))
        if not part:
            raise EOFError
        result += part
    return result


def send(kind, scope=None, attachments=(), **fields):
    global sequence
    frame = dict(wire_version=3, endpoint_token=token, sequence=sequence,
                 request_id=scope, operation=dict(kind=kind, **fields))
    sequence += 1
    if mode == "wrong_token" and kind == "hello":
        frame["endpoint_token"] = "0" * 64
    header = json.dumps(frame, separators=(",", ":")).encode()
    packet = struct.pack(">I", len(header)) + header + b"".join(attachments)
    if mode == "fragmented":
        for offset in range(0, len(packet), 3):
            peer.sendall(packet[offset:offset + 3])
    else:
        peer.sendall(packet)


def receive():
    global expected
    frame = json.loads(exact(struct.unpack(">I", exact(4))[0]))
    assert frame["wire_version"] == 3 and frame["endpoint_token"] == token
    assert frame["sequence"] == expected, (frame, expected)
    expected += 1
    op = frame["operation"]
    parts = [exact(op[key]) for key in ("observation_bytes", "response_example_bytes", "result_bytes") if key in op]
    record(event="receive", kind=op["kind"], request=frame["request_id"])
    return frame, parts


operations = ["validate_clauses", "evaluate_clauses", "history", "countermodel", "ledger", "strongest_refutations"]
# The current host revision. The default endpoint declares exactly it, so
# `fixture_push_for_tools` — which stamps the host constant — agrees with the
# agreement these tests negotiate. The "lower_revision" mode below is what
# covers a peer that declares an older one.
capabilities = dict(version="3.2.0", supported_operations=operations, required_operations=[])
if mode == "bad_major":
    capabilities["version"] = "2.0.0"
if mode == "lower_revision":
    # A compatible earlier revision, as a released client keeps declaring.
    capabilities["version"] = "3.0.0"
if mode == "missing_required":
    capabilities["supported_operations"] = ["missing"]
    capabilities["required_operations"] = ["missing"]
send("hello", capabilities=capabilities)
frame, _ = receive()
assert frame["operation"]["kind"] == "ready"
if mode in {"blocked_request", "blocked_reply"}:
    peer.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1024)
if mode == "blocked_request":
    record(event="blocked_request")
    time.sleep(60)
while True:
    frame, parts = receive()
    op = frame["operation"]
    scope = frame["request_id"]
    if op["kind"] == "shutdown":
        if mode == "ignore_shutdown":
            time.sleep(60)
        send("closed")
        raise SystemExit(0)
    if op["kind"] == "request_closed":
        continue
    assert op["kind"] == "request"
    observation, example = map(json.loads, parts)
    assert isinstance(observation, dict) and isinstance(example, dict)
    assert op["remaining_request_budget_ns"] is None or op["remaining_request_budget_ns"].isdigit()
    record(event="request", request=scope, remaining=op["remaining_request_budget_ns"])
    if mode == "blocked_reply":
        send("query", scope, [b"{}"], query_id=1, name="ledger", args_bytes=2)
        record(event="blocked_reply")
        time.sleep(60)
    if mode == "early_eof":
        raise SystemExit(0)
    if mode == "wrong_sequence":
        sequence += 1
    if mode == "wrong_scope":
        scope += 1
    if mode == "repeat_hello":
        send("hello", capabilities=capabilities)
        time.sleep(60)
    if mode == "query_gap":
        send("query", scope, [b"{}"], query_id=2, name="ledger", args_bytes=2)
        time.sleep(60)
    if mode == "complete_without_receipt":
        send("complete", scope, outcome="no_response" if mode == "submitted_no_response" else "response")
        continue
    if mode in ("no_response", "source_exhausted", "failure"):
        send("complete", scope, outcome=mode)
        continue
    if mode == "cancel":
        send("query", scope, [b"{}"], query_id=1, name="ledger", args_bytes=2)
        frame, _ = receive()
        assert frame["operation"]["kind"] == "cancel"
        record(event="cancel", reason=frame["operation"]["reason"])
        send("complete", scope, outcome="failure")
        continue
    if mode == "pending_complete":
        send("query", scope, [b"{}"], query_id=1, name="ledger", args_bytes=2)
        send("complete", scope, outcome="no_response")
        continue
    if mode == "queries":
        for query in [1, 2]:
            args = json.dumps({"delay": query == 1}).encode()
            send("query", scope, [args], query_id=query, name="ledger", args_bytes=len(args))
        replies = [receive()[0]["operation"] for _ in range(2)]
        assert [reply["query_id"] for reply in replies] == [2, 1]
    if mode == "invalid_query":
        send("query", scope, [b'{"x":1,"x":2}'], query_id=1, name="ledger", args_bytes=13)
        reply, data = receive()
        record(event="invalid_result", result=json.loads(data[0]))
    if mode == "detached":
        code = "import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(60)"
        child = subprocess.Popen([sys.executable, "-c", code], start_new_session=True)
        record(event="detached", pid=child.pid)
        # Give the host identity monitor a normal bounded scheduling interval.
        time.sleep(0.12)
    payload = b" {opaque exact \xce\xbb}\n"
    if mode == "empty":
        payload = b""
    if mode == "truncated_submit":
        send("submit", scope, [payload[:2]], bytes=len(payload))
        raise SystemExit(0)
    send("submit", scope, [payload], bytes=len(payload))
    receipt, _ = receive()
    record(event="receipt", kind=receipt["operation"]["kind"])
    if receipt["operation"]["kind"] == "rejected":
        continue
    assert receipt["operation"]["kind"] == "submitted"
    if mode == "duplicate":
        send("submit", scope, [b"ignored"], bytes=7)
        duplicate, _ = receive()
        assert duplicate["operation"] == {"kind": "rejected", "code": "duplicate_submission"}
    send("complete", scope, outcome="no_response" if mode == "submitted_no_response" else "response")
