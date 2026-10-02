#!/usr/bin/env python3
# Author: Fangzhu Shen
"""Standalone stdlib-only native MCP relay for C's private transport.

The relay knows no verifier, agent provider or MCP semantics. It carries opaque
lines and reserves bounded observed input before sending it. A reply reaches
native stdout, flushed, before the relay reads any further input.
"""

import os
import re
import socket
import struct
import sys


SOCKET_ENV = "WHIEL_AGENT_MCP_SOCKET"
TOKEN_ENV = "WHIEL_AGENT_MCP_TOKEN"
# The relay's stderr belongs to whatever started it, and a provider CLI keeps
# that stream to itself, so a relay failure would otherwise leave the owner with
# a closed socket and no reason. The relay also drops one bounded failure line
# beside its own socket, inside C's scratch directory, where only C reads it.
DIAGNOSTIC_SUFFIX = ".diagnostic"
DIAGNOSTIC_BYTES = 2048
MAX_CHUNK_BYTES = 64 * 1024
MAX_LINE_BYTES = 64 * 1024 * 1024
U64_MAX = (1 << 64) - 1
HEADER = struct.Struct(">cQI")
HELLO, READY, BEGIN, RESERVED = b"H", b"Y", b"B", b"R"
RESULT, EOF, CLOSED = b"O", b"E", b"C"
KINDS = frozenset((HELLO, READY, BEGIN, RESERVED, RESULT, EOF, CLOSED))


class RelayError(ValueError):
    """Invalid bounded C relay framing, without copying any native data."""


def require(condition, message):
    if not condition:
        raise RelayError(message)


def token_bytes(value):
    require(type(value) is str and re.fullmatch(r"[0-9a-f]{64}", value) is not None,
            "invalid C relay token")
    return bytes.fromhex(value)


def encode_header(kind, sequence, length=0):
    require(type(sequence) is int and 0 <= sequence <= U64_MAX, "invalid relay sequence")
    require(type(length) is int and 0 <= length <= MAX_LINE_BYTES, "invalid relay length")
    require(kind in KINDS, "invalid relay operation")
    require((kind == HELLO and length == 32)
            or (kind == BEGIN and 1 <= length <= MAX_CHUNK_BYTES)
            or kind == RESULT
            or (kind not in (HELLO, BEGIN, RESULT) and length == 0), "invalid relay operation length")
    return HEADER.pack(kind, sequence, length)


def decode_header(data):
    require(type(data) is bytes and len(data) == HEADER.size, "invalid relay header")
    kind, sequence, length = HEADER.unpack(data)
    encode_header(kind, sequence, length)
    return kind, sequence, length


def next_sequence(sequence):
    require(type(sequence) is int and 0 <= sequence < U64_MAX, "relay sequence exhausted")
    return sequence + 1


def read_exact(stream, length):
    require(type(length) is int and 0 <= length <= MAX_LINE_BYTES, "invalid relay read length")
    result = bytearray()
    while len(result) < length:
        part = stream.recv(min(MAX_CHUNK_BYTES, length - len(result)))
        if not part:
            raise EOFError("truncated C relay packet")
        result.extend(part)
    return bytes(result)


def reply(stream, expected, sequence):
    kind, actual_sequence, length = decode_header(read_exact(stream, HEADER.size))
    require(kind == expected and actual_sequence == sequence, "unexpected relay phase or sequence")
    return length


def write_all(output, data):
    view = memoryview(data)
    while view:
        length = output.write(view)
        if type(length) is not int or length <= 0 or length > len(view):
            raise OSError("native stdout did not accept reply")
        view = view[length:]


def run(input_stream, output_stream, socket_path, token):
    require(type(socket_path) is str and os.path.isabs(socket_path), "invalid C relay socket")
    identity = token_bytes(token)
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as stream:
        stream.connect(socket_path)
        stream.sendall(encode_header(HELLO, 0, len(identity)) + identity)
        reply(stream, READY, 0)
        sequence, line_bytes = 1, 0
        pending = b""
        read = getattr(input_stream, "read1", input_stream.read)
        while True:
            if not pending:
                pending = read(MAX_CHUNK_BYTES)
                require(type(pending) is bytes and len(pending) <= MAX_CHUNK_BYTES,
                        "invalid native input read")
            if not pending:
                if line_bytes:
                    raise EOFError("native input ended inside an MCP line")
                stream.sendall(encode_header(EOF, sequence))
                reply(stream, CLOSED, sequence)
                output_stream.flush()
                return
            newline = pending.find(b"\n")
            length = len(pending) if newline < 0 else newline + 1
            chunk = pending[:length]
            end_line = chunk.endswith(b"\n")
            # Announce an observed over-cap chunk before refusing its raw body;
            # C charges the observation before it decides whether to reserve it.
            stream.sendall(encode_header(BEGIN, sequence, length))
            reply(stream, RESERVED, sequence)
            require(line_bytes + length <= MAX_LINE_BYTES, "native MCP line exceeds bound")
            stream.sendall(chunk)
            pending = pending[length:]
            line_bytes = 0 if end_line else line_bytes + length
            output_bytes = reply(stream, RESULT, sequence)
            require(end_line or output_bytes == 0, "reply before complete input line")
            output = read_exact(stream, output_bytes)
            require(not output or (output.endswith(b"\n") and b"\n" not in output[:-1]),
                    "native reply is not one complete line")
            # Validate the entire reply before exposing any prefix to stdout.
            write_all(output_stream, output)
            output_stream.flush()
            sequence = next_sequence(sequence)


def failure_text(error, token):
    """Name the failing relay operation without echoing what it carried.

    A RelayError message is one of this file's own fixed strings, and an OSError
    reports its own errno text. Neither carries native data, but the connection
    token is scrubbed in case an operating-system message quotes an argument.
    """
    text = f"{type(error).__name__}: {error}"
    if type(token) is str and token:
        text = text.replace(token, "<token>")
    return text[:DIAGNOSTIC_BYTES].replace("\n", " ")


def write_diagnostic(socket_path, text):
    """Leave one bounded line beside the socket; never fail the exit status."""
    if type(socket_path) is not str or not os.path.isabs(socket_path):
        return
    try:
        descriptor = os.open(socket_path + DIAGNOSTIC_SUFFIX,
                             os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        with os.fdopen(descriptor, "w", encoding="utf-8", errors="replace") as target:
            target.write(text + "\n")
    except OSError:
        pass


def main():
    socket_path, token = os.environ.get(SOCKET_ENV), os.environ.get(TOKEN_ENV)
    try:
        run(sys.stdin.buffer, sys.stdout.buffer, socket_path, token)
    except (OSError, EOFError, RelayError) as error:
        write_diagnostic(socket_path, failure_text(error, token))
        # Tokens, paths, native data and provider diagnostics never enter stderr.
        print("C MCP relay failed", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
