"""PAPER REPRODUCTION CODE: shared support for the fixed paper commands."""
from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parents[1]
ARMS = ("whiel", "whiel-skills", "whiel-tools", "whiel-tools-skills")
MODELS = ("gpt-5.5", "gpt-5.6-sol", "gpt-6-astra")
ACCEPTED = {"valid_uncertified", "invalid_uncertified"}
STD3 = {"propext", "Classical.choice", "Quot.sound"}
DEFAULT_OUTPUT = "artifacts/paper-reproduction"


class ReproError(RuntimeError):
    """An unmet prerequisite or incomplete reproduction, never an unsolved task."""


class Interrupted(ReproError):
    pass


def require(condition, message):
    if not condition:
        raise ReproError(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def read_json(path):
    try:
        value = json.loads(Path(path).read_text())
    except (OSError, ValueError) as error:
        raise ReproError(f"Cannot read JSON record {Path(path).name}: {error}") from error
    require(isinstance(value, dict), f"Expected a JSON object: {Path(path).name}")
    return value


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    try:
        temporary.write_text(json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def digest(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def relative(repo, path):
    path = Path(path)
    path = path if path.is_absolute() else Path(repo) / path
    try:
        return path.resolve().relative_to(Path(repo).resolve()).as_posix()
    except ValueError as error:
        raise ReproError("Reproduction paths must stay inside the checkout.") from error


def resolve(repo, value):
    require(isinstance(value, (str, Path)), "A repository-relative path is required.")
    path = Path(value)
    require(not path.is_absolute() and ".." not in path.parts,
            "Use a repository-relative path without '..'.")
    destination = (Path(repo) / path).resolve()
    relative(repo, destination)
    return destination


def output_directory(repo, value=DEFAULT_OUTPUT):
    path = resolve(repo, value)
    artifacts = (Path(repo) / "artifacts").resolve()
    require(path != artifacts and path.is_relative_to(artifacts),
            "The output root must be a subdirectory of artifacts/.")
    return path


def benchmark_ids(repo):
    cases = sorted(p.name for p in (Path(repo) / "Benchmark").iterdir()
                   if re.fullmatch(r"Example[0-9]{4}", p.name) and (p / "Input.lean").is_file())
    require(len(cases) == 86, "The paper protocol requires the shipped 86-input benchmark.")
    return cases


@dataclass
class Context:
    repo: Path
    output_root: Path
    trial: Path | None = None
    manifest: dict | None = None

    def rel(self, path):
        return relative(self.repo, path)

    def path(self, value):
        return resolve(self.repo, value)

    @property
    def auth_root(self):
        return self.output_root / "auth"

    def save(self):
        require(self.trial is not None and self.manifest is not None, "No selected reproduction trial.")
        self.manifest["updated_at"] = now()
        atomic_json(self.trial / "manifest.json", self.manifest)


def new_trial(ctx):
    inputs = benchmark_ids(ctx.repo)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    trial = ctx.output_root / "runs" / (stamp + "-" + uuid.uuid4().hex[:8])
    trial.mkdir(parents=True, exist_ok=False)
    try:
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ctx.repo, text=True).strip()
    except (OSError, subprocess.CalledProcessError):
        revision = None
    identities = {f"Benchmark/{case}/Input.lean": digest(ctx.repo / "Benchmark" / case / "Input.lean")
                  for case in inputs}
    for path in ("lean-toolchain", "toolchain.lock.json", "lakefile.toml", "lake-manifest.json",
                 "agent_houdini/experiments/full-benchmark-lean-agent.json",
                 "agent_houdini/toolchain/cli-lock.json"):
        identities[path] = digest(ctx.repo / path)
    for arm in ARMS:
        path = f"agent_houdini/experiments/paper/{arm}.json"
        identities[path] = digest(ctx.repo / path)
    ctx.trial = trial
    ctx.manifest = {
        "schema_version": 1, "state": "prepared", "created_at": now(),
        "revision": revision, "inputs": inputs, "source_sha256": identities,
        "output_root": ctx.rel(ctx.output_root), "trial": ctx.rel(trial),
        "search": [{"arm": arm, "model": model, "state": "pending",
                    "inputs": inputs if index == 0 else None, "cases": []}
                   for arm in ARMS for index, model in enumerate(MODELS)],
        "direct_lean": {"state": "pending", "inputs": inputs},
        "certification": {"state": "pending", "expected_pairs": None, "attempts": []},
        "commands": [],
    }
    ctx.save()
    atomic_json(ctx.output_root / "current.json", {"schema_version": 1, "manifest": ctx.rel(trial / "manifest.json")})
    return ctx


def current_trial(repo, output_root):
    pointer = read_json(output_root / "current.json")
    require(pointer.get("schema_version") == 1, "Unsupported current-trial pointer.")
    manifest_path = resolve(repo, pointer.get("manifest"))
    require(manifest_path.is_relative_to(output_root / "runs"), "Current trial is outside its output root.")
    manifest = read_json(manifest_path)
    require(manifest.get("schema_version") == 1, "Unsupported reproduction manifest.")
    require(manifest.get("trial") == relative(repo, manifest_path.parent), "Trial identity mismatch.")
    return Context(Path(repo), Path(output_root), manifest_path.parent, manifest)


@contextmanager
def exclusive(output_root):
    output_root.mkdir(parents=True, exist_ok=True)
    with (output_root / ".reproduction.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ReproError("Another reproduction command owns this output root.") from error
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def lock_held(output_root):
    path = Path(output_root) / ".reproduction.lock"
    if not path.exists():
        return False
    with path.open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return True
        fcntl.flock(lock, fcntl.LOCK_UN)
    return False


def command(ctx, arguments, log=None, *, env=None, allowed=(0,), interactive=False, cleanup_group=False, cleanup_tree=False):
    """Run a public command and let its own interruption/cleanup handler finish."""
    arguments = [str(value) for value in arguments]
    entry = {"argv": arguments, "started_at": now(), "state": "starting"}
    if log is not None:
        entry["log"] = ctx.rel(log)
    if ctx.manifest is not None:
        ctx.manifest["commands"].append(entry)
        ctx.save()
    print("Running:", " ".join(arguments), flush=True)
    stream = None
    process = None
    tree = None
    require(not (interactive and (cleanup_group or cleanup_tree)), "Interactive login cannot use owned-tree cleanup.")
    interrupted = []
    previous = {}

    def stop(signum, _frame):
        interrupted.append(signum)
        if process is not None and process.poll() is None:
            if tree is not None:
                try:
                    tree.refresh()  # Remember descendants before their parent exits.
                except (OSError, subprocess.SubprocessError) as error:
                    entry["inspection_error"] = str(error)
            try:
                if cleanup_group:
                    os.killpg(process.pid, signal.SIGTERM)
                else:
                    process.send_signal(signal.SIGTERM)
            except ProcessLookupError:
                pass

    try:
        for sig in (signal.SIGINT, signal.SIGTERM):
            previous[sig] = signal.signal(sig, stop)
        if not interactive and log is not None:
            Path(log).parent.mkdir(parents=True, exist_ok=True)
            stream = Path(log).open("x")
        if interrupted:
            raise Interrupted("Interrupted before command launch.")
        process = subprocess.Popen(arguments, cwd=ctx.repo, env=env,
                                   stdout=stream, stderr=subprocess.STDOUT if stream else None,
                                   start_new_session=not interactive)
        if cleanup_group or cleanup_tree:
            from scripts.compare_certificate_builds import ProcessTree
            tree = ProcessTree(process.pid)
            tree.refresh()
        entry.update(state="running", pid=process.pid)
        if ctx.manifest is not None:
            ctx.save()
        if interrupted:
            stop(interrupted[-1], None)
        if tree is None:
            code = process.wait()
        else:
            while True:
                tree.refresh()
                try:
                    code = process.wait(timeout=0.2)
                    break
                except subprocess.TimeoutExpired:
                    continue
        entry.update(exit_code=code, state="interrupted" if interrupted else "finished")
        if interrupted:
            raise Interrupted("Interrupted; the child command has exited after cleanup.")
        require(code in allowed, f"Command exited {code}; inspect {entry.get('log', 'the output above')}.")
        return code
    except BaseException:
        entry["state"] = "interrupted" if interrupted else "failed"
        if process is not None and process.poll() is None:
            stop(signal.SIGTERM, None)
            process.wait()
        raise
    finally:
        cleanup_error = None
        try:
            if tree is not None:
                entry["cleanup_ok"] = tree.stop()
        except Exception as error:
            entry["cleanup_ok"] = False
            entry["cleanup_error"] = str(error)
            cleanup_error = error
        finally:
            for sig, handler in previous.items():
                signal.signal(sig, handler)
            if stream is not None:
                stream.close()
            entry["finished_at"] = now()
            if entry.get("cleanup_ok") is False or entry.get("inspection_error"):
                entry["state"] = "failed"
            if ctx.manifest is not None:
                ctx.save()
        if entry.get("cleanup_ok") is False or entry.get("inspection_error"):
            raise ReproError("Child inspection/cleanup failed; no further commands will start.") from cleanup_error


def successful_search_cases(ctx, *, require_complete=True):
    selected = {}
    for stage in ctx.manifest["search"]:
        if require_complete:
            require(stage["state"] in ("complete", "skipped"), "Search is incomplete; certification cannot start.")
        for row in stage.get("cases", []):
            if row.get("status") not in ACCEPTED:
                continue
            key = (stage["arm"], row["input"])
            selected.setdefault(key, dict(row, arm=stage["arm"], model=stage["model"]))
    return list(selected.values())
