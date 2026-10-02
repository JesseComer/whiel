#!/usr/bin/env python3
"""Public API peer for campaign resource gates; no engine or C imports."""

import json
import os
import socket
import struct
import subprocess
import sys
import time


def encoded(value):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode()


trace, byte_limit = sys.argv[1], int(sys.argv[2])
# "idle" holds an accepted consultation open with its own live child, so an
# interruption gate observes a real endpoint tree instead of a finished peer.
mode = sys.argv[3] if len(sys.argv) > 3 else "exhaust"
assert mode in ("exhaust", "idle"), mode
token = os.environ["WHIEL_PROPOSER_TOKEN"]
stream = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
stream.settimeout(120)
sent = received = traffic_bytes = 0
request_id = None


def log(kind, **fields):
    with open(trace, "ab") as output:
        output.write(encoded(dict(kind=kind, pid=os.getpid(), bytes=traffic_bytes, **fields)) + b"\n")


def envelope(sequence, kind, **fields):
    return dict(wire_version=3, endpoint_token=token, sequence=sequence,
                request_id=request_id, operation=dict(kind=kind, **fields))


def send(kind, padding=0, **fields):
    global sent, traffic_bytes
    header = encoded(envelope(sent, kind, **fields)) + b" " * padding
    assert 0 < len(header) <= 1024
    packet = struct.pack(">I", len(header)) + header
    stream.sendall(packet)
    traffic_bytes += len(packet)
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
    global received, traffic_bytes
    size, = struct.unpack(">I", exact(4))
    assert 0 < size <= 16384
    header = exact(size)
    value = json.loads(header)
    assert value["wire_version"] == 3 and value["endpoint_token"] == token
    assert value["sequence"] == received
    operation = value["operation"]
    assert operation["kind"] == expected, operation
    traffic_bytes += 4 + size
    if expected == "request":
        for field in ("observation_bytes", "response_example_bytes"):
            traffic_bytes += len(exact(operation[field]))
    received += 1
    return value


log("started")
stream.connect(os.environ["WHIEL_PROPOSER_SOCKET"])
send("hello", capabilities=dict(version="3.0.0", supported_operations=[], required_operations=[]))
receive("ready")
log("ready")
request = receive("request")
request_id = request["request_id"]
log("request", request_id=request_id)
if mode == "idle":
    child = subprocess.Popen(
        [sys.executable, "-I", "-c", "import time; time.sleep(3600)"],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    log("idle", child=child.pid)
    time.sleep(3600)
    raise SystemExit(99)
padding = 0
if byte_limit:
    # Use permitted JSON whitespace to leave precisely one byte after B's
    # RequestClosed packet. This refuses Shutdown without a timing/size guess.
    closing_bytes = 4 + len(encoded(envelope(received, "request_closed")))
    complete_bytes = 4 + len(encoded(envelope(sent, "complete", outcome="source_exhausted")))
    padding = byte_limit - traffic_bytes - closing_bytes - complete_bytes - 1
    assert 0 <= padding < 800, padding
send("complete", padding=padding, outcome="source_exhausted")
receive("request_closed")
log("request_closed")
request_id = None
try:
    receive("shutdown")
    log("shutdown")
    send("closed")
    log("closed")
except EOFError:
    log("transport_closed")
