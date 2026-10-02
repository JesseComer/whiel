# Author: Fangzhu Shen
"""Standalone relay safety: exact opaque bytes and bounded reads."""

import io
import threading
import unittest
from unittest.mock import patch

from agent_houdini import mcp_stdio as relay


TOKEN = "ab" * 32


class Stream:
    def __init__(self, data, fragment=2):
        self.incoming = data
        self.sent = bytearray()
        self.fragment = fragment
        self.closed = False
        self.read_sizes = []

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.closed = True

    def connect(self, path):
        self.path = path

    def recv(self, length):
        self.read_sizes.append(length)
        part = self.incoming[:min(length, self.fragment)]
        self.incoming = self.incoming[len(part):]
        return part

    def sendall(self, data):
        self.sent.extend(data)


def packet(kind, sequence, body=b""):
    return relay.encode_header(kind, sequence, len(body)) + body


def responses(output=b"reply\n"):
    return (packet(relay.READY, 0) + packet(relay.RESERVED, 1)
            + packet(relay.RESULT, 1, output) + packet(relay.CLOSED, 2))


class FragmentedOutput(io.BytesIO):
    def write(self, data):
        return super().write(bytes(data[:2]))


class RelayTests(unittest.TestCase):
    def run_relay(self, data, incoming, output=None):
        stream = Stream(incoming)
        output = output or FragmentedOutput()
        with patch.object(relay.socket, "socket", return_value=stream):
            relay.run(io.BytesIO(data), output, "/private/tmp/unused.sock", TOKEN)
        return stream, output

    def test_fragmented_stdio_and_packets_preserve_exact_unicode_and_opaque_bytes(self):
        raw = ' {"payload":"λ"} \n'.encode()
        answer = b' {"opaque":"\xff"}\n'
        stream, output = self.run_relay(raw, responses(answer))
        self.assertEqual(output.getvalue(), answer)
        expected = (packet(relay.HELLO, 0, relay.token_bytes(TOKEN))
                    + relay.encode_header(relay.BEGIN, 1, len(raw)) + raw
                    + packet(relay.EOF, 2))
        self.assertEqual(bytes(stream.sent), expected)
        self.assertTrue(stream.closed)

    def test_chunks_never_cross_line_boundaries_or_exceed_64_kib(self):
        first = b"x" * relay.MAX_CHUNK_BYTES
        incoming = (packet(relay.READY, 0) + packet(relay.RESERVED, 1) + packet(relay.RESULT, 1)
                    + packet(relay.RESERVED, 2) + packet(relay.RESULT, 2, b"one\n")
                    + packet(relay.RESERVED, 3) + packet(relay.RESULT, 3, b"two\n")
                    + packet(relay.CLOSED, 4))
        stream, output = self.run_relay(first + b"y\nnext\n", incoming)
        expected = (packet(relay.HELLO, 0, relay.token_bytes(TOKEN))
                    + relay.encode_header(relay.BEGIN, 1, len(first)) + first
                    + relay.encode_header(relay.BEGIN, 2, 2) + b"y\n"
                    + relay.encode_header(relay.BEGIN, 3, 5) + b"next\n"
                    + packet(relay.EOF, 4))
        self.assertEqual(bytes(stream.sent), expected)
        self.assertEqual(output.getvalue(), b"one\ntwo\n")

    def test_stdout_flush_completes_before_the_relay_reads_more_input(self):
        stream = Stream(responses())
        flushing, release = threading.Event(), threading.Event()
        failures = []
        class GatedOutput(FragmentedOutput):
            def flush(self):
                flushing.set()
                if not release.wait(2):
                    raise OSError("test flush timeout")
                return super().flush()
        output = GatedOutput()
        def run():
            try:
                with patch.object(relay.socket, "socket", return_value=stream):
                    relay.run(io.BytesIO(b"x\n"), output, "/private/tmp/unused.sock", TOKEN)
            except BaseException as error:
                failures.append(error)
        worker = threading.Thread(target=run)
        worker.start()
        try:
            self.assertTrue(flushing.wait(1))
            self.assertNotIn(packet(relay.EOF, 2), stream.sent)
        finally:
            release.set()
            worker.join(2)
        self.assertFalse(worker.is_alive())
        self.assertEqual(failures, [])
        self.assertIn(packet(relay.EOF, 2), stream.sent)

    def test_write_and_flush_failure_stop_the_relay(self):
        for failure in ("write", "flush"):
            stream = Stream(responses())
            class BrokenOutput(FragmentedOutput):
                def write(self, data):
                    if failure == "write":
                        raise OSError("private stdout detail")
                    return super().write(data)
                def flush(self):
                    if failure == "flush":
                        raise OSError("private flush detail")
                    return super().flush()
            with patch.object(relay.socket, "socket", return_value=stream), self.assertRaises(OSError):
                relay.run(io.BytesIO(b"x\n"), BrokenOutput(), "/private/tmp/unused.sock", TOKEN)
            self.assertNotIn(packet(relay.EOF, 2), stream.sent)

    def test_clean_eof_closes_but_partial_line_eof_fails(self):
        stream, output = self.run_relay(b"", packet(relay.READY, 0) + packet(relay.CLOSED, 1))
        self.assertEqual(output.getvalue(), b"")
        self.assertIn(packet(relay.EOF, 1), stream.sent)
        stream = Stream(packet(relay.READY, 0) + packet(relay.RESERVED, 1) + packet(relay.RESULT, 1))
        with patch.object(relay.socket, "socket", return_value=stream), self.assertRaises(EOFError):
            relay.run(io.BytesIO(b"partial"), FragmentedOutput(), "/private/tmp/unused.sock", TOKEN)
        self.assertNotIn(packet(relay.EOF, 2), stream.sent)

    def test_input_cap_includes_newline_and_announces_observed_overflow(self):
        with patch.object(relay, "MAX_LINE_BYTES", 64), patch.object(relay, "MAX_CHUNK_BYTES", 32):
            partial = packet(relay.READY, 0) + packet(relay.RESERVED, 1) + packet(relay.RESULT, 1)
            valid = partial + packet(relay.RESERVED, 2) + packet(relay.RESULT, 2, b"ok\n") + packet(relay.CLOSED, 3)
            stream, _ = self.run_relay(b"x" * 63 + b"\n", valid)
            self.assertIn(b"x" * 31 + b"\n", stream.sent)
            # Announce the last observed newline, but refuse its raw body even
            # if a faulty C peer reserves the accumulated over-cap line.
            incoming = partial + packet(relay.RESERVED, 2) + packet(relay.RESULT, 2) + packet(relay.RESERVED, 3)
            stream = Stream(incoming)
            with patch.object(relay.socket, "socket", return_value=stream), self.assertRaises(relay.RelayError):
                relay.run(io.BytesIO(b"x" * 64 + b"\n"), FragmentedOutput(), "/private/tmp/unused.sock", TOKEN)
            self.assertEqual(bytes(stream.sent)[-relay.HEADER.size:], relay.HEADER.pack(relay.BEGIN, 3, 1))
            self.assertNotIn(b"\n", stream.sent)

    def test_wrong_phase_sequence_and_malformed_header_never_reach_stdout(self):
        malformed = (relay.HEADER.pack(b"?", 1, 0), packet(relay.RESULT, 2, b"x\n"),
                     packet(relay.CLOSED, 1), relay.HEADER.pack(relay.RESULT, 1, relay.MAX_LINE_BYTES + 1))
        for result in malformed:
            stream = Stream(packet(relay.READY, 0) + packet(relay.RESERVED, 1) + result)
            output = FragmentedOutput()
            with patch.object(relay.socket, "socket", return_value=stream), self.assertRaises(relay.RelayError):
                relay.run(io.BytesIO(b"x\n"), output, "/private/tmp/unused.sock", TOKEN)
            self.assertEqual(output.getvalue(), b"")

    def test_truncated_result_never_exposes_partial_stdout(self):
        stream = Stream(packet(relay.READY, 0) + packet(relay.RESERVED, 1)
                        + relay.encode_header(relay.RESULT, 1, 10) + b"prefix")
        output = FragmentedOutput()
        with patch.object(relay.socket, "socket", return_value=stream), self.assertRaises(EOFError):
            relay.run(io.BytesIO(b"x\n"), output, "/private/tmp/unused.sock", TOKEN)
        self.assertEqual(output.getvalue(), b"")
        self.assertNotIn(packet(relay.EOF, 2), stream.sent)

    def test_invalid_line_shape_and_early_output_are_rejected(self):
        for data, result in ((b"x\n", b"missing newline"), (b"x\n", b"two\nlines\n"),
                             (b"partial", b"early\n")):
            output = FragmentedOutput()
            with self.assertRaises(relay.RelayError):
                self.run_relay(data, responses(result), output)
            self.assertEqual(output.getvalue(), b"")

    def test_invalid_token_and_sequence_exhaustion_fail_explicitly(self):
        for token in (None, "AB" * 32, "ab" * 31, "z" * 64):
            with self.assertRaises(relay.RelayError):
                relay.token_bytes(token)
        for sequence in (True, -1, relay.U64_MAX + 1):
            with self.assertRaises(relay.RelayError):
                relay.encode_header(relay.EOF, sequence)
        with self.assertRaises(relay.RelayError):
            relay.next_sequence(relay.U64_MAX)
        self.assertEqual(relay.next_sequence(0), 1)
        with self.assertRaises(relay.RelayError):
            relay.run(io.BytesIO(), io.BytesIO(), "relative.sock", TOKEN)


if __name__ == "__main__":
    unittest.main()
