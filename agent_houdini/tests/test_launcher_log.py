# Author: Fangzhu Shen
"""C-owned bounded logs and diagnostic redaction; no native calls."""

import json
import os
from pathlib import Path
import tempfile
import threading
import unittest

from agent_houdini.agent_log import AgentLog, DIAGNOSTIC_BYTES, WITHHELD, bounded_redacted_diagnostic


class AgentLogTests(unittest.TestCase):
    def test_diagnostic_text_remains_bounded_utf8_and_redacted(self):
        for text in ["upstream sk-private-fixture-token", "Bearer fixture", "--password secret",
                     "OPENAI_API_KEY=secret", '{"api_key":"private"}',
                     "https://user:private@proxy.invalid"]:
            self.assertEqual(bounded_redacted_diagnostic(text), WITHHELD)
        self.assertEqual(bounded_redacted_diagnostic("upstream unavailable"), "upstream unavailable")
        for limit in (0, 1, 3, DIAGNOSTIC_BYTES):
            result = bounded_redacted_diagnostic("é" * DIAGNOSTIC_BYTES, limit)
            self.assertLessEqual(len(result.encode()), limit)
            self.assertTrue(all(letter == "é" for letter in result))

    def test_log_is_exclusive_private_and_records_the_fields_c_supplies(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "events.jsonl"
            with AgentLog(path) as log:
                # Callers pass their own typed values; foreign text passes
                # bounded_redacted_diagnostic before it reaches the log.
                log.emit("native_start", {"model": "fixture-model", "version": "1",
                         "diagnostic": bounded_redacted_diagnostic("password=private")})
                log.emit("bad kind", {"value": 1})
            data = path.read_bytes()
            self.assertNotIn(b"private", data)
            self.assertEqual(path.stat().st_mode & 0o777, 0o600)
            self.assertEqual([json.loads(line)["kind"] for line in data.splitlines()],
                             ["native_start", "unknown_event"])
            event = json.loads(data.splitlines()[0])
            self.assertEqual(event["schema_version"], 1)
            self.assertEqual(event["fields"]["model"], "fixture-model")
            with self.assertRaises(FileExistsError):
                AgentLog(path)
            link = Path(temporary) / "linked"
            link.symlink_to(path)
            with self.assertRaises(FileExistsError):
                AgentLog(link)
            self.assertEqual(path.read_bytes(), data)

    def test_overflow_is_bounded_and_does_not_reset_after_oversized_event(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "events.jsonl"
            with AgentLog(path, maximum_bytes=300, maximum_events=2, record_bytes=200) as log:
                log.emit("huge", {"data": "λ" * 100000})
                for index in range(10):
                    log.emit("count", {"index": index})
                self.assertEqual(log.events_written, 2)
                self.assertEqual(log.dropped_events, 9)
                self.assertLessEqual(log.bytes_written, 300)
            self.assertEqual(len(path.read_bytes()), log.bytes_written)
            self.assertEqual([json.loads(line)["sequence"] for line in path.read_text().splitlines()], [0, 1])

    def test_nested_and_concurrent_events_remain_bounded_valid_json(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "events.jsonl"
            with AgentLog(path, maximum_events=10) as log:
                # An unencodable record is dropped, never partially written.
                value = {"child": None}
                value["child"] = value
                log.emit("cycle", value)
                threads = [threading.Thread(target=log.emit, args=("count", {"value": i})) for i in range(20)]
                for thread in threads:
                    thread.start()
                for thread in threads:
                    thread.join()
                self.assertEqual(log.dropped_events, 11)
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            self.assertEqual([row["sequence"] for row in rows], list(range(10)))
            self.assertTrue(all(row["kind"] == "count" for row in rows))
            self.assertEqual(os.stat(path).st_size, log.bytes_written)


if __name__ == "__main__":
    unittest.main()
