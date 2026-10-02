#!/usr/bin/env python3
"""A token-free replay proposer: the repository's own answer, no model at all.

This is a generic wire-3 proposer executable. B starts it exactly as it starts
the agent harness — `campaign run --proposer-executable` — and it answers each
request with the answer the repository already records for that input:

    Benchmark/<ID>/Core.json           the accepted Core rows, in level order
    Benchmark/<ID>/Counterexample.json the accepted counterexample instance

A valid case is submitted as `candidate_clauses` and an invalid one as
`candidate_counterexample`, through the same bounded proposal channel a real
agent uses, bound to the exact push. Nothing here asserts that the answer is
correct: B's untrusted verifier — the Vampire proof lane racing the
finite-model lane, the Lean worker and leveled Houdini — does exactly the work
it would do for an agent that proposed the right answer on its first
consultation.

So the expected outcome of a replay campaign over the solved corpus is that
**every solved case is accepted**. A rejection, a correction that never
settles, or a search that runs to its limit is a verifier incompleteness
defect, not a proposer mistake.

An input with neither record has no answer to replay. The proposer then
declines: it finishes the request as `source_exhausted` and closes the
endpoint, so B ends that input at once with a terminal endpoint failure
instead of holding the search open until its deadline.

Usage (B supplies the socket and token through the environment):

    replay_proposer.py --repo PATH [--log PATH] [--max-requests N]

This is harness test tooling, not part of the proposer runtime: it reads the
benchmark records a real proposer must never see, so it lives with the tests.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import socket
import struct
import sys


WIRE_VERSION = 3
API_VERSION = "3.0.0"
QUERIES = ("countermodel", "strongest_refutations", "history", "ledger",
           "validate_clauses", "evaluate_clauses")
MAXIMUM_PACKET = 64 * 1024 * 1024
MAXIMUM_HEADER = 16384
ATTACHMENTS = {"request": ("observation_bytes", "response_example_bytes"),
               "query_result": ("result_bytes",)}
CORE_KIND = "whiel_framework_ii_core_rows"
COUNTEREXAMPLE_KIND = "whiel_framework_ii_counterexample"
CORE_FILE = "Core.json"
COUNTEREXAMPLE_FILE = "Counterexample.json"
BENCHMARK_DIR = "Benchmark"
# A replayed answer that is right needs one request. A correction round can
# follow a host limit, so allow a few, then decline rather than loop to the
# search deadline. A transcript replay has no such cap of its own: the
# transcript says how many rounds there are, and cutting it short would replay
# a different search from the one recorded.
DEFAULT_MAXIMUM_REQUESTS = 4


class ReplayError(Exception):
    """The exchange or the recorded answer cannot be used."""


def encoded(value):
    return json.dumps(value, ensure_ascii=False, allow_nan=False,
                      separators=(",", ":")).encode("utf-8")


def require(condition, message):
    if not condition:
        raise ReplayError(message)


# --------------------------------------------------------------------------
# The recorded answer


def answers_directory(repo, answers=None):
    """Where the recorded answers live: `<directory>/<ID>/Core.json` or
    `Counterexample.json`.

    By default that is the repository's own `Benchmark/`. `answers` names
    another directory of the same shape instead -- a campaign's verifier
    destination, which holds the answers that run accepted -- and a harness
    run directory is taken to mean its `verifier/` subdirectory.
    """
    if answers is None:
        return Path(repo) / BENCHMARK_DIR
    directory = Path(answers)
    nested = directory / "verifier"
    return nested if nested.is_dir() else directory


def read_record(repo, identity, answers=None):
    """The recorded answer for one input, or None.

    Returns `("candidate_clauses", [source, ...])` for a valid case,
    `("candidate_counterexample", instance)` for an invalid one, and None when
    the input has neither record and there is nothing to replay.
    """
    require(isinstance(identity, str) and identity and "/" not in identity
            and "\\" not in identity and identity not in (".", ".."),
            "the push named no usable canonical input id")
    directory = answers_directory(repo, answers) / identity
    core = directory / CORE_FILE
    counterexample = directory / COUNTEREXAMPLE_FILE
    if core.is_file():
        return "candidate_clauses", core_clauses(_document(core), identity)
    if counterexample.is_file():
        return "candidate_counterexample", counterexample_instance(
            _document(counterexample), identity)
    return None


def _document(path):
    try:
        document = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise ReplayError(f"cannot read {path}: {error}") from error
    require(isinstance(document, dict), f"{path} is not a JSON object")
    return document


def core_clauses(document, identity):
    """The Core rows as clause sources, weakest level first."""
    require(document.get("kind") == CORE_KIND,
            f"{identity}: not a Framework II Core record")
    rows = document.get("rows")
    require(isinstance(rows, list) and rows, f"{identity}: no Core rows")
    ordered = []
    for row in rows:
        require(isinstance(row, dict), f"{identity}: a Core row is not an object")
        level, source = row.get("level"), row.get("source")
        require(isinstance(level, int) and not isinstance(level, bool) and level >= 0,
                f"{identity}: a Core row has no level")
        require(isinstance(source, str) and source,
                f"{identity}: a Core row has no clause source")
        ordered.append((level, source))
    # A stable sort keeps the recorded order inside one level and presents the
    # lower levels first, which is the order the record itself is written in.
    ordered.sort(key=lambda row: row[0])
    return [source for _, source in ordered]


def counterexample_instance(document, identity):
    """The recorded counterexample instance, exactly as the record holds it."""
    require(document.get("kind") == COUNTEREXAMPLE_KIND,
            f"{identity}: not a Framework II counterexample record")
    instance = document.get("instance")
    require(isinstance(instance, dict) and isinstance(instance.get("relations"), list),
            f"{identity}: the counterexample record carries no instance")
    for relation in instance["relations"]:
        require(isinstance(relation, dict) and isinstance(relation.get("name"), str)
                and isinstance(relation.get("rows"), list),
                f"{identity}: a counterexample relation is malformed")
    return {"relations": [{"name": relation["name"], "rows": relation["rows"]}
                          for relation in instance["relations"]]}


def build_response(example, kind, answer):
    """One proposal, bound to this request by the push's own response example."""
    require(isinstance(example, dict), "the response example is not a JSON object")
    binding = example.get("binding")
    schema_version = example.get("schema_version")
    require(isinstance(binding, dict), "the response example carries no binding")
    require(isinstance(schema_version, int) and not isinstance(schema_version, bool),
            "the response example carries no schema version")
    response = {"kind": kind, "schema_version": schema_version, "binding": binding}
    if kind == "candidate_clauses":
        response["clauses"] = list(answer)
        response["dropped"] = []
    else:
        response["input"] = answer
    return response


def push_identity(observation):
    """The canonical input id the push names."""
    try:
        return observation["feedback"]["presentation"]["task"]["canonical_id"]
    except (TypeError, KeyError):
        raise ReplayError("the push names no task") from None


def response_binding(example):
    """The live push's own binding, the one part of a transcript response
    that can never be replayed as recorded: every earlier field names the
    original run, but the binding names this one.
    """
    require(isinstance(example, dict), "the response example is not a JSON object")
    binding = example.get("binding")
    require(isinstance(binding, dict), "the response example carries no binding")
    return binding


class RecordSource:
    """The repository's own recorded answer, replayed unchanged for every
    consultation of one input: the original replay-proposer behavior.
    """

    # An input with no recorded answer at all has nothing to become right
    # later: declining at once and releasing the endpoint is the correct,
    # documented ending for this source (see the module docstring). Holding
    # is `TranscriptSource`'s own remedy for a different situation -- an
    # otherwise-answered input whose transcript runs out -- not this one's.
    HOLD_OPEN_ON_DECLINE = False

    def __init__(self, repo, answers=None):
        self.repo = repo
        self.answers = answers
        self._identity = None
        self._answer = None

    def response(self, observation, example, request_id):
        identity = push_identity(observation)
        if identity != self._identity:
            self._identity, self._answer = identity, read_record(self.repo, identity, self.answers)
        if self._answer is None:
            return None, "no recorded answer"
        return build_response(example, *self._answer), None


# --------------------------------------------------------------------------
# Transcript mode: a retained run's own recorded responses, replayed
# consultation by consultation instead of the repository's single answer.


PENDING_HEADER = re.compile(r"^# Pending clauses \(\d+\)\s*$", re.M)
PENDING_CLAUSE = re.compile(r"^    clause (\d+)  minimum level")
SECTION_END = re.compile(r"^(?:# |={10,})", re.M)


def _section(text, header):
    """The body of one rendered `# ...` prompt section, verbatim.

    Bounded by the next top-level heading or rule, the same way the harness's
    own offline digest reads a recorded prompt (`experiment.py`'s `_section`);
    duplicated here rather than imported, since this tool is read-only test
    tooling that a real proposer must never import.
    """
    match = header.search(text)
    if not match:
        return ""
    rest = text[match.end():]
    end = SECTION_END.search(rest)
    return rest if not end else rest[:end.start()]


def recorded_pending_sources(prompt_text):
    """clause_id -> the clause text a recorded prompt's own "Pending clauses"
    section printed for it.

    That section is where a drop reference's clause identity, printed at the
    same request under IDENTITIES AND DROP REFERENCES, is described in text
    rather than digests: `_clause_lines` in `prompt.py` prints the verifier's
    `canonical_source` (or, failing that, `display`) indented beneath the
    clause's own header line, one clause at a time. Reconstructing that text
    here is how a recorded drop, whose identity is this run's own and useless
    in a new one, is later matched against a live push's pending list by what
    the clause actually says.
    """
    sources, current = {}, None
    for line in _section(prompt_text, PENDING_HEADER).split("\n"):
        header = PENDING_CLAUSE.match(line)
        if header:
            current = []
            sources[int(header.group(1))] = current
            continue
        if current is None:
            continue
        if line.startswith("        displayed:"):
            current = None  # the source text block for this clause is over
        elif line.startswith("        "):
            current.append(line[8:])
        else:
            current = None
    return {identifier: "\n".join(lines) for identifier, lines in sources.items() if lines}


def _clause_text(clause):
    if not isinstance(clause, dict):
        return None
    source = clause.get("canonical_source")
    return source if isinstance(source, str) and source else clause.get("display")


def live_pending_drop_references(observation):
    """clause text -> the live push's own drop reference, for every pending
    clause it currently authorizes a drop for.
    """
    feedback = observation.get("feedback") if isinstance(observation, dict) else {}
    pending = feedback.get("pending") if isinstance(feedback, dict) else None
    found = {}
    for entry in pending if isinstance(pending, list) else ():
        if not isinstance(entry, dict):
            continue
        reference = entry.get("drop_reference")
        text = _clause_text(entry.get("clause"))
        if isinstance(reference, dict) and isinstance(text, str) and text:
            found.setdefault(text, reference)
    return found


def remap_drops(dropped, recorded_sources, live_references, *, on_omit):
    """A recorded run's `dropped` list, re-pointed at the live push.

    Each entry names a clause of the run being replayed by an identity that
    means nothing in this one. It is re-found by its own text: the recorded
    clause id looks up that text in `recorded_sources` (the same request's
    own recorded prompt), and the text looks up the live drop reference in
    `live_references` (the live push's own pending list). A clause that
    cannot be found either way -- the recorded prompt did not show it, or the
    live push is not currently offering a drop for that text -- is left out
    and reported through `on_omit`, never invented or guessed at.
    """
    remapped = []
    for entry in dropped:
        clause = entry.get("clause") if isinstance(entry, dict) else None
        clause_id = clause.get("clause_id") if isinstance(clause, dict) else None
        text = recorded_sources.get(clause_id) if isinstance(clause_id, int) else None
        reference = live_references.get(text) if text else None
        if reference is None:
            on_omit(clause_id)
            continue
        remapped.append(reference)
    return remapped


TRANSCRIPT_FILE_KIND = "whiel_transcript_replay"


class TranscriptSource:
    """A retained transcript's own recorded responses, one per consultation,
    each re-bound to a new live push -- from a retained run directory (the
    original shape) or from a single `export-transcript` JSON file (a small,
    publishable freeze of one run's own transcripts; see
    `agent_houdini/export_transcript.py`), told apart by `path` being a
    directory or a file.

    Consultation N (the endpoint's own request id) answers with the content
    the original proposer submitted at its own consultation N -- exactly the
    payload it sent, including one that was malformed there, so the
    verifier's handling of it is exercised again -- with only `binding`
    replaced by the live push's own. A consultation the transcript has
    nothing recorded for, and the end of the transcript, both report `None`
    to `serve`, which -- because `END_SEARCH_ON_DECLINE` is set -- ends the
    search there and then by closing the connection, instead of declining
    (see `serve`'s own docstring for why: declining a still-open search does
    not end the input, and holding it open just spends the rest of the
    search limit).
    """

    END_SEARCH_ON_DECLINE = True

    def __init__(self, path):
        path = Path(path)
        self._file = _FrozenTranscript(path) if path.is_file() else None
        self.run_dir = path

    def response(self, observation, example, request_id):
        if self._file is not None:
            return self._file.response(observation, example, request_id)
        return self._directory_response(observation, example, request_id)

    def _directory_response(self, observation, example, request_id):
        identity = push_identity(observation)
        directory = self.run_dir / "agent" / identity / f"request-{request_id}"
        if not directory.is_dir():
            return None, "end of the recorded transcript"
        payload = _last_submission_payload(directory / "submissions.jsonl")
        if payload is None:
            return None, "the recorded transcript has no submission for this consultation"
        response = dict(payload)
        response["binding"] = response_binding(example)
        dropped = response.get("dropped")
        if isinstance(dropped, list) and dropped:
            recorded_sources = recorded_pending_sources(_read_text(directory / "prompt.txt"))
            live_references = live_pending_drop_references(observation)

            def omit(clause_id):
                print(f"replay proposer: {identity}: request {request_id}: cannot map "
                      f"recorded drop (clause {clause_id}) to the live push; omitting it",
                      file=sys.stderr, flush=True)

            response["dropped"] = remap_drops(dropped, recorded_sources, live_references, on_omit=omit)
        return response, None


class _FrozenTranscript:
    """One `export-transcript` JSON file's own recorded responses.

    Its `dropped` entries are already resolved to clause text at export time
    (`export_transcript.py` reads the original run's own recorded prompts for
    this, once, so a frozen transcript never needs them again) -- `None`
    where the original could not resolve one. Remapping a dropped clause to
    the live push's own drop reference is therefore a single lookup by text,
    with no recorded prompt to parse.
    """

    def __init__(self, path):
        try:
            document = json.loads(Path(path).read_text(encoding="utf-8"))
        except (OSError, ValueError) as error:
            raise ReplayError(f"cannot read transcript {path}: {error}") from error
        require(isinstance(document, dict) and document.get("kind") == TRANSCRIPT_FILE_KIND,
                f"{path} is not a {TRANSCRIPT_FILE_KIND} file")
        inputs = document.get("inputs")
        self.inputs = inputs if isinstance(inputs, dict) else {}

    def response(self, observation, example, request_id):
        identity = push_identity(observation)
        record = self.inputs.get(identity)
        requests = record.get("requests") if isinstance(record, dict) else None
        entry = next((item for item in requests or []
                     if isinstance(item, dict) and item.get("number") == request_id), None)
        if entry is None:
            return None, "end of the recorded transcript"
        payload = entry.get("submission")
        if not isinstance(payload, dict):
            return None, "the recorded transcript has no submission for this consultation"
        response = dict(payload)
        response["binding"] = response_binding(example)
        dropped = response.get("dropped")
        if isinstance(dropped, list) and dropped:
            live_references = live_pending_drop_references(observation)
            remapped = []
            for text in dropped:
                reference = live_references.get(text) if isinstance(text, str) else None
                if reference is None:
                    print(f"replay proposer: {identity}: request {request_id}: cannot map "
                         f"recorded drop ({text!r}) to the live push; omitting it",
                         file=sys.stderr, flush=True)
                    continue
                remapped.append(reference)
            response["dropped"] = remapped
        return response, None


def _read_text(path):
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _last_submission_payload(path):
    """The last submitted `payload`, parsed, from one recorded consultation's
    `submissions.jsonl` -- or None when it does not exist or holds nothing
    usable, meaning the original proposer never submitted this consultation.
    """
    if not path.is_file():
        return None
    payload = None
    try:
        with open(path, encoding="utf-8") as source:
            for line in source:
                line = line.strip()
                if not line:
                    continue
                try:
                    record = json.loads(line)
                except ValueError:
                    continue
                candidate = record.get("payload") if isinstance(record, dict) else None
                if not isinstance(candidate, str):
                    continue
                try:
                    document = json.loads(candidate)
                except ValueError:
                    continue
                if isinstance(document, dict):
                    payload = document
    except OSError:
        return None
    return payload


# --------------------------------------------------------------------------
# The wire


class Endpoint:
    """One wire-3 connection, for one verifier input."""

    def __init__(self, path, token, log=None):
        self.token = token
        self.log_path = log
        self.stream = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.stream.settimeout(300)
        self.stream.connect(path)
        self.sent = self.received = 0
        self.request_id = None

    def close(self):
        try:
            self.stream.close()
        except OSError:
            pass

    def log(self, kind, **fields):
        if not self.log_path:
            return
        try:
            with open(self.log_path, "ab") as output:
                output.write(encoded({"kind": kind, "pid": os.getpid(),
                                      "request_id": self.request_id, **fields}) + b"\n")
        except OSError:
            pass

    def _exact(self, length):
        require(type(length) is int and 0 <= length <= MAXIMUM_PACKET, "invalid length")
        value = bytearray()
        while len(value) < length:
            part = self.stream.recv(min(length - len(value), 65536))
            require(part, "truncated packet")
            value.extend(part)
        return bytes(value)

    def send(self, kind, attachments=(), **fields):
        header = encoded({"wire_version": WIRE_VERSION, "endpoint_token": self.token,
                          "sequence": self.sent, "request_id": self.request_id,
                          "operation": {"kind": kind, **fields}})
        require(len(header) <= MAXIMUM_HEADER, "oversized header")
        require(4 + len(header) + sum(map(len, attachments)) <= MAXIMUM_PACKET,
                "oversized packet")
        self.stream.sendall(struct.pack(">I", len(header)) + header + b"".join(attachments))
        self.sent += 1

    def receive(self, expected):
        size, = struct.unpack(">I", self._exact(4))
        require(0 < size <= MAXIMUM_HEADER, "oversized incoming header")
        frame = json.loads(self._exact(size))
        require(set(frame) == {"wire_version", "endpoint_token", "sequence",
                               "request_id", "operation"}, "unexpected envelope")
        require(frame["wire_version"] == WIRE_VERSION
                and frame["endpoint_token"] == self.token, "wrong API identity")
        require(frame["sequence"] == self.received, "wrong incoming sequence")
        self.received += 1
        operation = frame["operation"]
        require(operation["kind"] in expected,
                "unexpected operation: " + str(operation["kind"]))
        lengths = [operation[key] for key in ATTACHMENTS.get(operation["kind"], ())]
        require(4 + size + sum(lengths) <= MAXIMUM_PACKET, "oversized attachments")
        return frame, [self._exact(length) for length in lengths]

    def handshake(self):
        self.send("hello", capabilities={"version": API_VERSION,
                                         "supported_operations": list(QUERIES),
                                         "required_operations": []})
        frame, _ = self.receive({"ready"})
        require(frame["request_id"] is None, "the handshake is endpoint scoped")

    def submit(self, response):
        payload = encoded(response)
        self.send("submit", (payload,), bytes=len(payload))
        frame, _ = self.receive({"submitted", "rejected", "cancel"})
        kind = frame["operation"]["kind"]
        if kind != "submitted":
            self.log("not_submitted", operation=frame["operation"])
            return False
        require(frame["request_id"] == self.request_id, "wrong submission receipt")
        self.log("submitted", bytes=len(payload), response_kind=response["kind"])
        return True

    def complete(self, outcome):
        self.send("complete", outcome=outcome)
        frame, _ = self.receive({"request_closed"})
        require(frame["request_id"] == self.request_id, "wrong closure receipt")
        self.log("complete", outcome=outcome)
        self.request_id = None


def serve(endpoint, source, maximum_requests=DEFAULT_MAXIMUM_REQUESTS):
    """Answer every request of one input; return the endpoint's exit status.

    `source` is a `RecordSource` (the repository's single recorded answer) or
    a `TranscriptSource` (a retained run's own responses, one per
    consultation); either way it is asked, request by request, for the
    response to submit or a reason to decline.

    A decline is not the same thing for the two sources. `RecordSource`
    completes it at once as `source_exhausted` and releases the endpoint:
    the input has no recorded answer at all, so there is nothing further to
    offer and no reason to hold the request open. `TranscriptSource` instead
    ends the search itself, at once, by closing the connection without
    completing the open request, when its own `source.response` reports
    `END_SEARCH_ON_DECLINE` -- the transcript has run out for an input that
    was otherwise being replayed. The reason is what a *completed* decline
    actually does to a live search: every wire outcome C can complete a
    request with -- `source_exhausted`, `no_response`, even `failure` -- is a
    per-consultation outcome, not a per-input one, and completing any of them
    while the search's own deadline has not yet arrived is published to the
    proposer as an ordinary correctable failure: the verifier opens a fresh
    consultation on the same exhausted input, which this proposer would
    decline again, and again, consultation after consultation -- each one a
    retained record under full retention -- until the search's own deadline,
    or, on a long enough input, the workspace guard first. This was measured
    directly against the real verifier: completing with `failure` or
    `no_response` both reproduce the spin, tens of thousands of consultations
    within a search limit of tens of seconds.

    Closing the connection outright -- never completing the open request,
    never answering `hello` again -- is different: the verifier reads that as
    its endpoint having exited before finishing, a transport-level fault
    rather than a proposal outcome, which is not republished to a fresh
    consultation the way a completed decline is. Measured against the real
    verifier this ends the input on the order of ten milliseconds, as
    `incomplete`/`InfrastructureFailure`, and the campaign proceeds to its
    next input exactly as it would after any other input's ordinary end --
    no resource guard, no delay, nothing further from this proposer. That
    `InfrastructureFailure` reads differently from the original run's own
    ending (`search_timeout` if the model's answer was never accepted) is
    expected and is why a transcript replay's fidelity checks (see
    `compare_runs.py`) treat every non-accepted status as one class rather
    than comparing the exact word.
    """
    endpoint.handshake()
    endpoint.log("ready")
    while True:
        frame, attachments = endpoint.receive({"request", "shutdown", "cancel"})
        kind = frame["operation"]["kind"]
        if kind == "shutdown":
            require(frame["request_id"] is None, "the shutdown is endpoint scoped")
            endpoint.send("closed")
            endpoint.log("closed", reason=frame["operation"]["reason"])
            return 0
        if kind == "cancel":
            endpoint.request_id = frame["request_id"]
            endpoint.complete("failure")
            continue
        request_id = frame["request_id"]
        require(type(request_id) is int and request_id >= 1, "a request needs an id")
        endpoint.request_id = request_id
        observation, example = (json.loads(part) for part in attachments)
        identity = push_identity(observation)
        endpoint.log("request", identity=identity)
        # Reaching the request cap means the same answer has already been
        # submitted that many times without settling, so it ends the search
        # the way an exhausted transcript does: a completed decline after
        # earlier responses is reopened as a fresh consultation, and only a
        # closed connection ends the input at once.
        capped = maximum_requests is not None and request_id > maximum_requests
        if capped:
            response, reason = None, f"more than {maximum_requests} requests"
        else:
            response, reason = source.response(observation, example, request_id)
        if response is None:
            if capped or getattr(source, "END_SEARCH_ON_DECLINE", False):
                endpoint.log("ending_search", identity=identity, reason=reason)
                print(f"replay proposer: {identity}: ending the search ({reason}): "
                      f"closing the connection so the verifier ends this input at once",
                      file=sys.stderr, flush=True)
                # Deliberately not `endpoint.complete(...)`: every outcome C
                # can complete a still-open request with -- source_exhausted,
                # no_response, even failure -- is a per-consultation result,
                # and completing one before the search's own deadline arrives
                # is published back to the proposer as a correctable failure,
                # which reopens a fresh consultation on this same exhausted
                # input rather than ending it (see `serve`'s own docstring for
                # the measurement). Closing the connection outright is read as
                # the endpoint having exited before finishing -- a
                # transport-level fault the verifier does not reopen -- which
                # ends the input at once instead.
                endpoint.close()
                return 0
            endpoint.log("declined", identity=identity, reason=reason)
            print(f"replay proposer: {identity}: declining, {reason}",
                  file=sys.stderr, flush=True)
            # Finish this request as exhausted; B ends the input at once
            # rather than holding the search open to its deadline, and then
            # closes the endpoint the same way it closes an accepted one. The
            # loop goes back to `receive` for that `shutdown`, exactly like
            # every other path here: declining is not a reason to hang up
            # before B says to, and doing so once was read as a transport
            # failure instead of the clean exhaustion it was.
            endpoint.complete("source_exhausted")
            continue
        if endpoint.submit(response):
            endpoint.complete("response")
        else:
            endpoint.complete("failure")


def main(argv=None):
    parser = argparse.ArgumentParser(description="Replay a recorded answer.")
    parser.add_argument("--repo", required=True,
                        help="repository root holding Benchmark/<ID>/")
    parser.add_argument("--transcript", default=None, metavar="RUN_DIR_OR_TRANSCRIPT_JSON",
                        help="replay a retained run directory's, or an export-transcript JSON "
                             "file's, own recorded responses, consultation by consultation, "
                             "instead of the repository's single recorded Core/Counterexample "
                             "answer")
    parser.add_argument("--answers", default=None, metavar="DIRECTORY",
                        help="read each input's recorded answer from DIRECTORY/<ID>/ instead of "
                             "the repository's Benchmark/<ID>/: a campaign's verifier "
                             "destination, or a harness run directory, holds the answers that "
                             "run accepted")
    parser.add_argument("--log", default=None,
                        help="optional JSONL trace of this endpoint's exchange")
    parser.add_argument("--max-requests", type=int, default=None,
                        help="requests answered before declining (default: 4 for an answer "
                             "replay; none for a transcript replay, which its transcript bounds)")
    options = parser.parse_args(argv)
    try:
        path = os.environ["WHIEL_PROPOSER_SOCKET"]
        token = os.environ["WHIEL_PROPOSER_TOKEN"]
    except KeyError as error:
        print(f"replay proposer: B supplies {error.args[0]}", file=sys.stderr)
        return 2
    if options.answers and options.transcript:
        print("replay proposer: give --answers or --transcript, not both", file=sys.stderr)
        return 2
    if options.max_requests is None and not options.transcript:
        options.max_requests = DEFAULT_MAXIMUM_REQUESTS
    if options.max_requests is not None and options.max_requests < 1:
        print("replay proposer: --max-requests must be at least 1", file=sys.stderr)
        return 2
    endpoint = Endpoint(path, token, log=options.log)
    source = (TranscriptSource(options.transcript) if options.transcript
             else RecordSource(options.repo, options.answers))
    try:
        return serve(endpoint, source, options.max_requests)
    except (ReplayError, OSError, ValueError) as error:
        endpoint.log("failed", error=repr(error))
        print(f"replay proposer: {error}", file=sys.stderr)
        return 1
    finally:
        endpoint.close()


if __name__ == "__main__":
    sys.exit(main())
