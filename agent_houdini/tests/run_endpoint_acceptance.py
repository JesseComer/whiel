#!/usr/bin/env python3
# Author: Fangzhu Shen
"""Run isolated C variants through one unchanged public verifier executable.

This is an opt-in integration gate with synthetic native agents, not a model
benchmark. Each successful case must produce a newly checked std3 certificate.
The CLI is proof-only; retained-model coverage is a separate real-FMB B gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time


VARIANTS = ("baseline", "prompt", "selection", "push", "skills", "model",
            "session", "mcp", "sandbox", "helper")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def inventory(directory):
    return {str(path.relative_to(directory)): digest(path)
            for path in sorted(directory.rglob("*")) if path.is_file()
            and "__pycache__" not in path.parts and path.suffix != ".pyc"}


def protected_inventory(repo, binary):
    names = subprocess.check_output(["git", "ls-files", "-z", "Databases", "Whiel",
        "whiel_runner/src", "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json"],
        cwd=repo).decode().split("\0")
    return {"sources": {name: digest(repo / name) for name in names if name},
            "binary_sha256": digest(binary)}


def replace(path, before, after):
    source = path.read_text()
    if source.count(before) != 1:
        raise ValueError(f"fixture patch no longer matches exactly once: {path.name}")
    path.write_text(source.replace(before, after))


SESSION_MODULE = '''"""Fixture-only retained C session helper; no API handle crosses requests."""
import asyncio
import sys
from .agent_runtime import NativeAgentRuntime as BaseRuntime

class NativeAgentRuntime(BaseRuntime):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.helper = None
    async def run(self, turn):
        if self.helper is None:
            code = "import sys\\nn=0\\nfor line in sys.stdin:\\n n+=1; print(n,flush=True)"
            self.helper = await asyncio.create_subprocess_exec(sys.executable, "-u", "-c", code,
                stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE)
        self.helper.stdin.write(b"turn\\n")
        await self.helper.stdin.drain()
        count = int(await asyncio.wait_for(self.helper.stdout.readline(), 2))
        self.events.emit("fixture_session", {"pid": self.helper.pid, "turn": count})
        return await super().run(turn)
    async def shutdown(self):
        try:
            await super().shutdown()
        finally:
            if self.helper is not None:
                self.helper.stdin.close()
                try:
                    await asyncio.wait_for(self.helper.wait(), 2)
                except asyncio.TimeoutError:
                    self.helper.kill()
                    await self.helper.wait()
'''

SANDBOX_MODULE = '''"""Fixture-only stricter Mac native sandbox, wholly owned by C."""
import json
from pathlib import Path
from .provider_runtime import CommandSpec

def wrap(args, environment, scratch):
    config = json.loads(args[args.index("--mcp-config") + 1])
    socket = config["mcpServers"]["whiel"]["env"]["WHIEL_AGENT_MCP_SOCKET"]
    sockets = sorted({socket, str(Path(socket).resolve())})
    profile = "(version 1)\\n(allow default)\\n(deny network*)\\n"
    for name in sockets:
        profile += "(allow network-outbound (literal " + json.dumps(name) + "))\\n"
    path = scratch / "fixture-network-deny.sb"
    path.write_text(profile)
    return CommandSpec(("/usr/bin/sandbox-exec", "-f", str(path), *args), environment, scratch)
'''


def variant(package, name):
    """All edits are in this disposable C package; B source is copied unchanged."""
    environment, arguments = {}, ["--model", "model-a"]
    if name == "prompt":
        replace(package / "prompt.py", '    lines = [RULE, "THIS CONSULTATION", RULE, ""]',
                '    lines = ["C-only changed introduction.", "", RULE, "THIS CONSULTATION", RULE, ""]')
    elif name == "selection":
        replace(package / "prompt.py", "        encode(observation).decode(\"utf-8\"),",
                '        encode({"feedback": {"presentation": {"ambient_schema": observation["feedback"]["presentation"]["ambient_schema"]}}, "correction": observation["correction"]}).decode("utf-8"),')
    elif name == "push":
        replace(package / "prompt.py", '    return "\\n\\n".join([*sections, tail]).encode("utf-8")',
                '    return (encode(observation) + b"\\nC builds this push.\\n"\n            + "\\n\\n".join([*sections, tail]).encode("utf-8"))')
    elif name == "skills":
        path = package / "acceptance-skills.json"
        path.write_text(json.dumps({"acceptance": "C-local fixture guidance"}))
        environment["WHIEL_AGENT_SKILLS_FILE"] = str(path)
    elif name == "model":
        # Any provider string passes through; C keeps no model table.
        arguments = ["--model", "model-b", "--reasoning-effort", "high"]
    elif name == "session":
        (package / "_acceptance_session.py").write_text(SESSION_MODULE)
        replace(package / "launcher.py", "from .agent_runtime import NativeAgentRuntime",
                "from ._acceptance_session import NativeAgentRuntime")
    elif name == "mcp":
        # C owns how an authorized query is presented; the query itself is
        # unchanged, so this varies the advertised description text only.
        replace(package / "tool_catalog.py",
                '"Read ledger history; use a returned continuation cursor for another page.",',
                '"C-owned ledger description for this variant; the same public query runs.",')
    elif name == "sandbox":
        if sys.platform != "darwin" or not Path("/usr/bin/sandbox-exec").is_file():
            raise RuntimeError("Mac stricter-sandbox variant unavailable on this platform")
        (package / "_acceptance_sandbox.py").write_text(SANDBOX_MODULE)
        replace(package / "providers/claude.py", "return CommandSpec(tuple(args), environment, scratch)",
                "from .._acceptance_sandbox import wrap\n    return wrap(args, environment, scratch)")
    elif name == "helper":
        helper = package / "_acceptance_formatter.py"
        helper.write_text('import sys\nif __name__ == "__main__":\n    sys.stdout.write("C helper changed this prompt.\\n" + sys.stdin.read())\n')
        replace(package / "prompt.py", '    return "\\n\\n".join([*sections, tail]).encode("utf-8")',
                '    import subprocess\n    import sys\n    from pathlib import Path\n    helper = Path(__file__).with_name("_acceptance_formatter.py")\n    rendered = "\\n\\n".join([*sections, tail])\n    return subprocess.run([sys.executable, str(helper)], input=rendered, text=True, capture_output=True, check=True, timeout=5).stdout.encode("utf-8")')
    elif name != "baseline":
        raise ValueError("unknown C variant")
    return environment, arguments


def process_exists(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False


def check_trace(case, name):
    rows = [json.loads(line) for line in (case / "native-trace.jsonl").read_text().splitlines()]
    starts = [row for row in rows if row["kind"] == "native_start"]
    submitted = [row for row in rows if row["kind"] == "submitted"]
    assert len(starts) >= 2 and len(submitted) >= 2, "missing real native correction rounds"
    assert not submitted[0]["correction_seen"] and submitted[1]["correction_seen"]
    for row in submitted:
        assert row["payload_sha256"] == hashlib.sha256(row["payload"].encode()).hexdigest()
    assert all(not process_exists(row["pid"]) for row in starts), "native child remains alive"
    assert all(not process_exists(row["relay_pid"]) for row in rows if row["kind"] == "relay_start"), "relay remains alive"
    tools = {row["request"]["params"]["name"] for row in rows if row["kind"] == "mcp"
             and row["request"]["method"] == "tools/call"}
    assert {"validate_clauses", "evaluate_clauses", "submit", "ledger"} <= tools
    if name == "mcp":
        listed = [row for row in rows if row["kind"] == "mcp"
                  and row["request"]["method"] == "tools/list"]
        assert listed and all("C-owned ledger description" in json.dumps(row["reply"]) for row in listed)
    if name == "prompt": assert "C-only changed introduction." in starts[0]["prompt"]
    if name == "selection":
        assert '"global_rev"' not in starts[0]["prompt"]
    if name == "push": assert starts[0]["prompt"].startswith("{")
    if name == "skills": assert any(row["kind"] == "local_skill" for row in rows)
    if name == "model": assert all(row["model"] == "model-b" for row in starts)
    if name == "helper": assert "C helper changed this prompt." in starts[0]["prompt"]
    if name == "sandbox": assert any(row["kind"] == "sandbox_denied" for row in rows)
    logs = [json.loads(line) for path in (case / "logs").rglob("*.jsonl") for line in path.read_text().splitlines()]
    if name == "session":
        sessions = [row["fields"] for row in logs if row["kind"] == "fixture_session"]
        assert [row["turn"] for row in sessions] == list(range(1, len(starts) + 1))
        assert len({row["pid"] for row in sessions}) == 1 and not process_exists(sessions[0]["pid"])
    return {"native_requests": len(starts), "tools": sorted(tools), "native_trace_sha256": digest(case / "native-trace.jsonl"),
            "payload_sha256": [row["payload_sha256"] for row in submitted]}


def run_case(args, name):
    case = args.evidence / name
    case.mkdir()
    copied = case / "source"
    package = copied / "agent_houdini"
    shutil.copytree(args.c_root / "agent_houdini", package,
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    shutil.copytree(args.repo / "whiel_runner/src", copied / "whiel_runner/src")
    original_c = inventory(package)
    original_b = inventory(copied / "whiel_runner/src")
    env_delta, c_arguments = variant(package, name)
    fixture = package / "tests/fixtures/endpoint_acceptance.py"
    fixture.chmod(0o755)
    fixture.with_suffix(".json").write_text(json.dumps({"synthetic_fixture": True,
        "trace": str(case / "native-trace.jsonl"), "require_network_denied": name == "sandbox"}))
    for folder in ("logs", "claude-config"):
        (case / folder).mkdir(mode=0o700)
    guard = subprocess.run([sys.executable, str(args.repo / "scripts/check_proposer_boundary.py"),
                            "--root", str(copied)], capture_output=True, text=True)
    (case / "source-check.log").write_text(guard.stdout + guard.stderr)
    assert guard.returncode == 0, "unchanged source gate rejected C-only variation"
    assert inventory(copied / "whiel_runner/src") == original_b
    before = protected_inventory(args.repo, args.binary)
    command = ["bash", str(args.repo / "scripts/watchdog.sh"), "4194304", sys.executable,
        str(package / "__main__.py"), "campaign", "run", "--verifier", str(args.binary),
        "--provider", "claude", "--provider-cli", str(fixture), "--agent-scratch-parent", "/private/tmp",
        "--agent-log-parent", str(case / "logs"), *c_arguments, "--", "--repo", str(args.repo),
        "--input", "Example0001", "--destination", str(case / "campaign"),
        "--worker", str(args.repo / ".lake/build/bin/fixed_ambient_encoding_worker"),
        "--search-limit", "240", "--certification-limit", "300", "--consultation-limit", "60",
        "--iteration-limit", "5", "--retention", "all"]
    environment = dict(os.environ, LEAN_NUM_THREADS="1", CLAUDE_CONFIG_DIR=str(case / "claude-config"))
    environment.update(env_delta)
    started = time.monotonic()
    receipt = {"variant": name, "result": "FAIL", "command": command, "before": before,
               "c_changes": {path: digest_value for path, digest_value in inventory(package).items()
                             if original_c.get(path) != digest_value},
               "scope": "real C launcher/native/MCP/public B and fresh proof-only certificate; no model, no retained-FMB claim"}
    try:
        with (case / "stdout.log").open("wb") as stdout, (case / "stderr.log").open("wb") as stderr:
            process = subprocess.Popen(command, cwd=args.repo, env=environment, stdout=stdout,
                                       stderr=stderr, start_new_session=True)
            try:
                code = process.wait(timeout=660)
            except subprocess.TimeoutExpired:
                listing = subprocess.check_output(["ps", "-Ao", "pid=,ppid="], text=True)
                for row in listing.splitlines():
                    pid, parent = map(int, row.split())
                    if parent == process.pid:
                        try: os.kill(pid, signal.SIGINT)
                        except ProcessLookupError: pass
                try: process.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    receipt["forced_cleanup"] = True
                raise
        receipt["returncode"] = code
        assert code == 0, "public C campaign failed"
        summary = json.loads((case / "campaign/summary.json").read_text())
        assert summary["schema_version"] == 3 and summary["all_certified"] is True
        assert len(summary["results"]) == 1
        certified = summary["results"][0]
        assert certified["status"] == "valid"
        assert set(certified["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
        certificate = Path(certified["certificate"])
        assert certificate.is_relative_to(case / "campaign") and (certificate / "Valid.lean").is_file()
        receipt["trace"] = check_trace(case, name)
        receipt["after"] = protected_inventory(args.repo, args.binary)
        assert receipt["before"] == receipt["after"], "A/B source or binary changed"
        assert original_b == inventory(copied / "whiel_runner/src"), "copied B source changed"
        receipt.update(result="PASS", summary=summary, certificate_files={
            str(path.relative_to(certificate)): digest(path) for path in certificate.rglob("*") if path.is_file()})
    except BaseException as error:
        receipt["error"] = repr(error)
        raise
    finally:
        receipt["seconds"] = time.monotonic() - started
        (case / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"variant": name, "result": "PASS", "seconds": receipt["seconds"],
                      "receipt": str(case / "receipt.json")}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path, help="built verifier checkout; read-only sources")
    parser.add_argument("--c-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--variant", choices=VARIANTS, action="append")
    args = parser.parse_args()
    for name in ("repo", "c_root", "binary", "evidence"):
        setattr(args, name, getattr(args, name).resolve())
    args.evidence.mkdir(parents=True, exist_ok=False)
    for name in args.variant or VARIANTS:
        run_case(args, name)


if __name__ == "__main__":
    main()
