"""Token-free GNU Parallel/real-bwrap overlap and isolation gate (Linux).

Only synthetic credentials and Python probes are used. No model, login or
network request occurs. This tests the native auth-lock path, not a mock.
"""
import argparse
import json
import os
from pathlib import Path
import shlex
import socket
import subprocess
import sys
import tempfile
import threading

from . import experiment


PROBE = r'''
import json, os, pathlib, socket, sys, time
work, slot, *denied = sys.argv[1:-1]
work = pathlib.Path(work)
auth = pathlib.Path(os.environ["CODEX_HOME"]) / "auth.json"
assert auth.read_text().startswith("synthetic-worker-" + slot)
for path in denied:
    assert not pathlib.Path(path).exists(), path
assert set(auth.parent.iterdir()) == {auth}
with socket.socket(socket.AF_UNIX) as client:
    client.connect(str(work / "bridge.sock"))
    client.sendall(b"ready")
    assert client.recv(2) == b"go"
started = time.monotonic()
# One short first-wave job proves immediate refill before the other three end.
time.sleep(0.2 if work.name not in {"job-2", "job-3", "job-4"} else 2)
with auth.open("a") as stream:
    stream.write("\n" + work.name)
(work / "observed.json").write_text(json.dumps({
    "slot": int(slot), "start": started, "end": time.monotonic(),
    "work": work.name, "private_auth_only": True, "other_work_hidden": True}))
'''


def probe(root, slot, number):
    root = Path(root)
    work = root / f"job-{number}"
    python = Path("/usr/bin/python3").resolve()
    home = root / "home"
    provider_home = home / f"worker-{slot}"
    denied = [str(home / f"worker-{other}" / "auth.json")
              for other in range(1, 5) if other != slot]
    denied += [str(root / f"job-{other}") for other in range(1, 9) if other != number]
    denied += [str(experiment.PACKAGE_ROOT / "TODO.md")]
    env = {"PATH": "/usr/bin:/bin", "HOME": str(home), "CODEX_HOME": str(provider_home),
           "WHIEL_BWRAP_PROVIDER": "codex", "WHIEL_BWRAP_WORK": str(work),
           "WHIEL_BWRAP_RO": json.dumps([str(python)]), "WHIEL_BWRAP_AUTH": "required",
           "WHIEL_BWRAP_TIMEOUT_SECS": "15"}
    return subprocess.call([str(experiment.PACKAGE_ROOT / "agent_houdini/bwrap.sh"),
                            "--", str(python), "-c", PROBE, str(work), str(slot),
                            *denied, 'cli_auth_credentials_store="file"'], env=env)


def check(parallel):
    with tempfile.TemporaryDirectory(prefix="whiel-pool-check-") as temporary:
        root = Path(temporary)
        for slot in range(1, 5):
            home = root / "home" / f"worker-{slot}"
            home.mkdir(parents=True, mode=0o700)
            auth = home / "auth.json"
            auth.write_text(f"synthetic-worker-{slot}")
            auth.chmod(0o600)
        barrier = threading.Barrier(4, timeout=12)
        errors = []
        servers = []
        def serve(number, listener):
            try:
                with listener:
                    listener.settimeout(20)
                    connection, _ = listener.accept()
                    with connection:
                        connection.settimeout(15)
                        assert connection.recv(5) == b"ready"
                        if number <= 4:
                            barrier.wait()
                        connection.sendall(b"go")
            except Exception as error:
                errors.append(type(error).__name__)
        for number in range(1, 9):
            work = root / f"job-{number}"
            work.mkdir(mode=0o700)
            listener = socket.socket(socket.AF_UNIX)
            listener.bind(str(work / "bridge.sock"))
            listener.listen(1)
            server = threading.Thread(target=serve, args=(number, listener))
            server.start()
            servers.append(server)
        child = shlex.join([sys.executable, "-m", "agent_houdini.pool_preflight",
                            "probe", str(root)]) + " {%} {}"
        result = subprocess.run([parallel, "--plain", "--will-cite", "-j4",
                                 "--halt", "soon,fail=1", "--joblog", str(root / "jobs.tsv"),
                                 child, ":::" , *map(str, range(1, 9))],
                                cwd=experiment.PACKAGE_ROOT, capture_output=True, text=True)
        for server in servers:
            server.join()
        if result.returncode or errors:
            raise RuntimeError(f"real concurrency probe failed: {errors}; {result.stderr}")
        rows = [json.loads((root / f"job-{number}" / "observed.json").read_text())
                for number in range(1, 9)]
        assert len({row["slot"] for row in rows[:4]}) == 4
        assert max(row["start"] for row in rows[:4]) < min(row["end"] for row in rows[:4])
        assert rows[4]["start"] < min(row["end"] for row in rows[1:4])
        events = sorted([(row["start"], 1) for row in rows]
                        + [(row["end"], -1) for row in rows])
        active = peak = 0
        for _, change in events:
            active += change
            peak = max(peak, active)
        assert peak == 4 and active == 0
        for slot in range(1, 5):
            seen = (root / "home" / f"worker-{slot}" / "auth.json").read_text().splitlines()[1:]
            assert sorted(seen) == sorted(row["work"] for row in rows if row["slot"] == slot)
        # All wrapper processes exited; all four real auth locks can be reacquired.
        from .bwrap import acquire_auth_lock
        import time
        for slot in range(1, 5):
            descriptor = acquire_auth_lock(root / "home" / f"worker-{slot}" / "auth.json",
                                           time.monotonic() + 1, lambda: False)
            os.close(descriptor)
        print(json.dumps({"status": "passed", "model_calls": 0, "jobs": 8,
                          "peak_native_concurrency": peak, "first_four_overlap": True,
                          "immediate_refill": True, "auth_refresh_isolated": True,
                          "other_auth_and_work_hidden": True, "locks_released": True,
                          "native_intervals": rows}, indent=2))
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "probe"])
    parser.add_argument("path")
    parser.add_argument("slot", type=int, nargs="?")
    parser.add_argument("number", type=int, nargs="?")
    args = parser.parse_args()
    raise SystemExit(check(args.path) if args.command == "check"
                     else probe(args.path, args.slot, args.number))
