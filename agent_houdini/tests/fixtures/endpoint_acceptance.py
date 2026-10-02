#!/usr/bin/env python3
# Author: Fangzhu Shen
"""Synthetic Claude CLI for public-boundary acceptance; no provider or API imports.

Only its sidecar configuration, native argv, prompt and MCP are consumed. Fixed
Example0001 candidate strings are test inputs; no certificates or B files are read.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


CLAUSES = ["(op_zS = (op_zE ∪ π[0,3] (σ[#1 = #2] ((op_zE × op_zT)))))",
           "(π[0,3] (σ[#1 = #2] ((op_zT × yp_zT))) ⊆ yp_zT)"]


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


RELATION_ROW = re.compile(r"^    (\S+)\s+(\S+)\s+(.+?)\s+(\d+|\?)\s+\S.*$")
CLAUSE_ROW = re.compile(r"^    clause (\d+)  ")
IDENTITY_ROW = re.compile(r"^    clause (\d+): (\{.*\})$")
CORRECTION_ROW = re.compile(r"^    ([a-z_]+): (.*)$")
CORRECTION_HEADING = "# Correction on your previous response"


def _section(prompt, heading):
    """The lines of one rendered section, up to the next heading or rule."""
    # The heading is a line of its own; the same words inside the prose
    # (the pending section names the identity tail) do not open a section.
    lines = prompt.split("\n")
    start = next((index for index, line in enumerate(lines) if line.startswith(heading)), None)
    if start is None:
        return []
    body, lines = lines[start + 1:], []
    for line in body:
        # A delimited heading sits between two rules; the one right under it
        # opens the section, any later one closes it.
        if line.startswith("=====") and not any(item.strip() for item in lines):
            continue
        if line.startswith("# ") or line.startswith("====="):
            break
        lines.append(line)
    return lines


def rendered_observation(prompt):
    """The push as C rendered it, in the observation's shape.

    C stopped appending the whole observation on 2026-09-17; its relation
    table, correction section, clause sections and the identity tail carry
    what this fixture reads: the relation keys, whether a correction is being
    answered and which codes it names, and the identity of every clause each
    list shows. Nothing here is a verifier fact the fixture did not read from
    the prompt.
    """
    identities = {}
    for line in _section(prompt, "IDENTITIES AND DROP REFERENCES"):
        match = IDENTITY_ROW.match(line)
        if not match:
            continue
        try:
            value = json.loads(match.group(2))
        except ValueError:
            continue
        # The tail lists identities (`clause_id`, digests) and, in the same
        # line shape, drop references (`clause`, digests); only the former
        # names a clause the sections show.
        if isinstance(value, dict) and "clause_id" in value:
            identities[int(match.group(1))] = value

    def clauses(heading):
        found = []
        for line in _section(prompt, heading):
            match = CLAUSE_ROW.match(line)
            if match:
                identifier = int(match.group(1))
                found.append({"clause": identities.get(identifier, {"clause_id": identifier})})
        return found

    relations = []
    for line in _section(prompt, "# Relations"):
        match = RELATION_ROW.match(line)
        if match and match.group(1) != "push":
            arity = match.group(4)
            relations.append({"key": match.group(1), "arity": int(arity) if arity.isdigit() else None})
    correction = None
    if CORRECTION_HEADING in prompt:
        correction = {"diagnostics": [
            {"code": match.group(1), "message": match.group(2)}
            for match in map(CORRECTION_ROW.match, _section(prompt, CORRECTION_HEADING)) if match]}
    return {"correction": correction,
            "feedback": {"presentation": {"ambient_schema": {"relations": relations}},
                         "core": clauses("# Current Core"), "pending": clauses("# Pending clauses"),
                         "last_round": clauses("# Last round")}}


def prompt_objects(prompt):
    """Find the public documents independently of C's prose/order.

    The response example is a complete JSON document in the prompt. The
    observation is read from a JSON document too when the prompt carries one
    (prompts recorded before 2026-09-17 did), and otherwise from the rendered
    sections, which is where a current prompt states it.
    """
    decoder = json.JSONDecoder()
    index = 0
    observation = example = None
    while index < len(prompt):
        start = prompt.find("{", index)
        if start < 0:
            break
        try:
            value, length = decoder.raw_decode(prompt[start:])
        except ValueError:
            index = start + 1
            continue
        index = start + length
        if isinstance(value, dict):
            if "feedback" in value and "correction" in value:
                observation = value
            if value.get("kind") == "candidate_clauses" and "binding" in value:
                example = value
    if observation is None and "# Relations" in prompt:
        observation = rendered_observation(prompt)
    require(observation is not None and example is not None, "missing public prompt documents")
    return observation, example


def _clause_id(reference):
    return reference.get("clause_id") if isinstance(reference, dict) else reference


def call_result(rpc, name, arguments):
    reply = rpc("tools/call", {"name": name, "arguments": arguments})
    require("result" in reply and not reply["result"].get("isError"), "MCP query refused")
    return json.loads(reply["result"]["content"][0]["text"])


def inspect_and_propose(rpc, observation, response, tools, record):
    names = {tool["name"] for tool in tools}
    ledger_name = "inspect_ledger" if "inspect_ledger" in names else "ledger"
    before = call_result(rpc, ledger_name, {})
    # A presentation-only tool returns its single canonical envelope.
    require(before["tool"] == "ledger" and "result" in before, "missing canonical ledger")
    validation = call_result(rpc, "validate_clauses", {"clauses": CLAUSES})["result"]
    require(len(validation["results"]) == 2 and all(x.get("admitted") is True
            for x in validation["results"]), "semantic validation rejected fixture clauses")
    schema = observation["feedback"]["presentation"]["ambient_schema"]
    instance = {"carrier_keys": ["num:0"], "relations": [
        {"name": relation["key"], "rows": []} for relation in schema["relations"]]}
    evaluation = call_result(rpc, "evaluate_clauses", {"clauses": CLAUSES,
        "instances": [{"kind": "supplied", "instance": instance}]})["result"]
    require(evaluation["instances"] == [{"kind": "supplied", "source_index": 0}]
            and not evaluation["skipped"] and len(evaluation["results"]) == 2
            and all(x.get("admitted") is True and x.get("holds") == [True]
                    for x in evaluation["results"]), "unexpected supplied-instance truth")
    if "get_skill" in names:
        skill = call_result(rpc, "get_skill", {"id": "acceptance"})
        require(skill == {"id": "acceptance", "content": "C-local fixture guidance"},
                "wrong local skill snapshot")
        record("local_skill", value=skill)
    after = call_result(rpc, ledger_name, {})
    require(before == after, "semantic reads changed the ledger")
    record("read_only_ledger", state_revision=before["state_revision"])
    response["clauses"] = CLAUSES
    correction = observation["correction"] is not None
    if not correction:
        response["binding"]["request_digest"] = "0" * 64
    payload = " \n" + json.dumps(response, ensure_ascii=False, separators=(",", ":")) + "\n "
    reply = rpc("tools/call", {"name": "submit", "arguments": {"payload": payload}})
    require("result" in reply and not reply["result"].get("isError"), "no submission receipt")
    record("submitted", correction_seen=correction, payload=payload,
           payload_sha256=hashlib.sha256(payload.encode()).hexdigest())



REFUTABLE = "(op_zE = ∅[2])"


def submit_proposal(rpc, response, observation, record):
    payload = " \n" + json.dumps(response, ensure_ascii=False, separators=(",", ":")) + "\n "
    reply = rpc("tools/call", {"name": "submit", "arguments": {"payload": payload}})
    require("result" in reply and not reply["result"].get("isError"), "no submission receipt")
    record("submitted", correction_seen=observation["correction"] is not None, payload=payload,
           payload_sha256=hashlib.sha256(payload.encode()).hexdigest())


def inspect_full_models(rpc, observation, response, tools, record):
    """Obtain every reference from public results; never read engine artifacts."""
    before = call_result(rpc, "ledger", {})
    validation = call_result(rpc, "validate_clauses", {"clauses": CLAUSES})["result"]
    require(len(validation["results"]) == 2 and all(row.get("admitted") is True
            for row in validation["results"]), "semantic admission refused clauses")
    schema = observation["feedback"]["presentation"]["ambient_schema"]
    instance = {"carrier_keys": ["num:0"], "relations": [
        {"name": relation["key"], "rows": []} for relation in schema["relations"]]}
    evaluated = call_result(rpc, "evaluate_clauses", {"clauses": CLAUSES,
        "instances": [{"kind": "supplied", "instance": instance}]})["result"]
    require(evaluated["instances"] == [{"kind": "supplied", "source_index": 0}]
            and evaluated["skipped"] == [] and len(evaluated["results"]) == 2
            and all(row.get("admitted") is True and row.get("holds") == [True]
                    for row in evaluated["results"]), "wrong supplied instance result")
    references, cursors = [], set()
    page = before["result"]
    for _ in range(256):
        for row in page["items"]:
            reference = row.get("clause", row.get("target"))
            if reference is not None and reference not in references:
                references.append(reference)
        cursor = page["metadata"]["continuation"]
        if cursor is None:
            break
        require(cursor not in cursors, "repeated ledger cursor")
        cursors.add(cursor)
        page = call_result(rpc, "ledger", {"cursor": cursor})["result"]
    else:
        raise ValueError("ledger fixture page bound exhausted")
    refuted = False
    for reference in references:
        history = call_result(rpc, "history", {"clause": reference})["result"]
        strongest = call_result(rpc, "strongest_refutations", {"clause": reference})["result"]
        for check in history["attempts"]:
            result = check["result"]
            if result["outcome"]["kind"] != "refuted":
                continue
            attempt = result["attempt_id"]
            require(type(attempt) is int and strongest["refutations"], "missing exposed refutation")
            model = call_result(rpc, "countermodel", {"attempt": attempt})["result"]
            require(model["attempt"] == attempt and isinstance(model.get("model"), dict),
                    "saved model unavailable")
            evaluated = call_result(rpc, "evaluate_clauses", {"clauses": [REFUTABLE],
                "instances": [{"kind": "retained", "attempt": attempt}]})["result"]
            require(evaluated["instances"] == [{"kind": "retained", "source_index": 0, "attempt": attempt}]
                    and evaluated["skipped"] == [] and len(evaluated["results"]) == 1
                    and evaluated["results"][0].get("admitted") is True
                    and evaluated["results"][0].get("holds") == [False], "saved model does not refute clause")
            refuted = True
    require(call_result(rpc, "ledger", {}) == before, "model queries changed ledger")
    response["clauses"] = CLAUSES
    if not refuted:
        if observation["correction"] is None:
            response["binding"]["request_digest"] = "0" * 64
        else:
            response["clauses"] = [REFUTABLE]
    record("full_models", refutation_seen=refuted)
    submit_proposal(rpc, response, observation, record)


def inspect_historical(rpc, observation, response, tools, record):
    """Read an old dead clause, then prove that reading grants no drop right."""
    if observation["correction"] is not None:
        require(any(item.get("code") == "drop_target_not_eligible"
                    for item in observation["correction"]["diagnostics"]), "wrong drop correction")
        response["clauses"], response["dropped"] = [], []
        submit_proposal(rpc, response, observation, record)
        return
    arguments, cursors, discovered = {}, set(), None
    for pages in range(1, 257):
        page = call_result(rpc, "ledger", arguments)["result"]
        require(len(page["items"]) == 1, "historical fixture requires one-row pages")
        row = page["items"][0]
        if row["kind"] == "attempt" and row["result"]["outcome"]["kind"] == "refuted":
            discovered = row
            break
        cursor = page["metadata"]["continuation"]
        require(cursor is not None and cursor not in cursors, "historical refutation not discoverable")
        cursors.add(cursor)
        arguments = {"cursor": cursor}
    require(discovered is not None and pages > 1, "historical clause was not beyond first page")
    clause, attempt = discovered["clause"], discovered["result"]["attempt_id"]
    for name in ("core", "pending", "last_round"):
        require(all(_clause_id(item["clause"]) != _clause_id(clause)
                    for item in observation["feedback"][name]),
                "historical clause is initially displayed")
    history = call_result(rpc, "history", {"clause": clause})["result"]
    require(history["clause"] == clause and history["status"].get("kind") == "dead" and history["status"].get("cause") == "refuted"
            and history["current_level"] is None, "historical clause is not dead/refuted")
    require(any(check["clause"] == clause and check["result"]["attempt_id"] == attempt
                and check["result"]["outcome"]["kind"] == "refuted" for check in history["attempts"]),
            "discovered attempt missing from history")
    model = call_result(rpc, "countermodel", {"attempt": attempt})["result"]
    require(model["attempt"] == attempt and model["clause"] == clause
            and model["model"]["relations"], "historical model unavailable")
    evaluated = call_result(rpc, "evaluate_clauses", {"clauses": [REFUTABLE],
        "instances": [{"kind": "retained", "attempt": attempt}]})["result"]
    require(evaluated["results"][0].get("admitted") is True
            and evaluated["results"][0].get("holds") == [False]
            and evaluated["instances"] == [{"kind": "retained", "source_index": 0, "attempt": attempt}],
            "historical evaluation mismatch")
    record("discovered", clause=clause, attempt=attempt, pages=pages)
    response["clauses"] = []
    response["dropped"] = [{"clause": clause,
        "consultation_digest": response["binding"]["consultation_digest"], "authorization_digest": "0" * 64}]
    submit_proposal(rpc, response, observation, record)

def run(configuration, arguments):
    require(configuration.get("synthetic_fixture") is True, "explicit synthetic fixture required")
    if arguments == ["--version"]:
        print("9.9.9 (fixture CLI)")
        return 0
    require("--mcp-config" in arguments and "--allowedTools" in arguments, "native Claude argv required")
    server = json.loads(arguments[arguments.index("--mcp-config") + 1])["mcpServers"]["whiel"]
    require(set(server["env"]) == {"WHIEL_AGENT_MCP_SOCKET", "WHIEL_AGENT_MCP_TOKEN"},
            "native relay received non-C capabilities")
    require(not any(key.startswith("WHIEL_PROPOSER_") for key in os.environ),
            "native CLI received verifier bootstrap credentials")
    trace = Path(configuration["trace"])
    def record(kind, **fields):
        with trace.open("a", encoding="utf-8") as stream:
            stream.write(json.dumps({"kind": kind, "pid": os.getpid(), **fields}, ensure_ascii=False) + "\n")
    if configuration.get("require_network_denied"):
        import socket
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as network:
                network.bind(("127.0.0.1", 0))
        except PermissionError:
            record("sandbox_denied")
        else:
            raise ValueError("stricter C sandbox did not deny network binding")
    prompt = sys.stdin.read()
    observation, response = prompt_objects(prompt)
    record("native_start", prompt=prompt, correction=observation["correction"],
           argv=arguments, model=arguments[arguments.index("--model") + 1])
    environment = dict(os.environ, **server["env"])
    relay = subprocess.Popen([server["command"], *server.get("args", [])], env=environment,
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    record("relay_start", relay_pid=relay.pid)
    sequence = 0
    def rpc(method, params=None):
        nonlocal sequence
        sequence += 1
        request = {"jsonrpc": "2.0", "id": sequence, "method": method}
        if params is not None:
            request["params"] = params
        wire = (json.dumps(request, ensure_ascii=False) + "\n").encode()
        relay.stdin.write(wire)
        relay.stdin.flush()
        result = relay.stdout.readline()
        require(result.endswith(b"\n"), "incomplete MCP reply")
        reply = json.loads(result)
        record("mcp", request=request, reply=reply)
        return reply
    try:
        rpc("initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                           "clientInfo": {"name": "boundary-fixture", "version": "1"}})
        tools = rpc("tools/list")["result"]["tools"]
        names = ["mcp__whiel__" + tool["name"] for tool in tools]
        require(sorted(names) == sorted(arguments[arguments.index("--allowedTools") + 1].split(",")),
                "native advertised tool inventory mismatch")
        # An installed CLI also lists its own built-in tools and the MCP
        # servers the account loaded, and reports its error fields as null.
        print(json.dumps({"type": "system", "subtype": "init",
                          "tools": ["Bash", "Read", "Write", "EndConversation", *names],
                          "model": arguments[arguments.index("--model") + 1],
                          "claude_code_version": "2.1.273", "apiKeySource": "none",
                          "permissionMode": "dontAsk", "plugins": [],
                          "plugin_errors": None, "mcp_server_errors": None,
                          "mcp_servers": [{"name": "connector-a", "status": "connected"},
                                          {"name": "whiel", "status": "connected"}]}), flush=True)
        scenario = configuration.get("scenario", "certificate")
        require(scenario in ("certificate", "full", "historical"), "unknown acceptance scenario")
        proposer = {"certificate": inspect_and_propose, "full": inspect_full_models,
                    "historical": inspect_historical}[scenario]
        proposer(rpc, observation, response, tools, record)
        relay.stdin.close()
        require(relay.wait(timeout=5) == 0, "standalone relay failed to close")
        record("native_closed")
        return 0
    finally:
        if relay.poll() is None:
            relay.kill()
        relay.wait()


if __name__ == "__main__":
    config = json.loads(Path(__file__).with_suffix(".json").read_text())
    raise SystemExit(run(config, sys.argv[1:]))
