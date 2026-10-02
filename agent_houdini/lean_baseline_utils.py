"""File records and input/auth discovery shared by the standalone Lean baseline."""

import hashlib
import json
import os
from pathlib import Path
import re
import stat
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RESPONSE_BYTES = 256 * 1024


def selected_inputs(resolved):
    """Enumerate input names only; the verifier still admits/checks each input."""
    benchmark = Path(resolved["repo"]) / "Benchmark"
    available = sorted(path.name for path in benchmark.iterdir()
                       if path.is_dir() and not path.is_symlink()
                       and re.fullmatch(r"Example[A-Za-z0-9_]+", path.name)
                       and (path / "Input.lean").is_file())
    inputs = available if resolved["all_inputs"] else resolved["inputs"]
    if not inputs or len(set(inputs)) != len(inputs):
        raise ValueError("pool inputs must be nonempty and unique")
    if any(identity not in available for identity in inputs):
        raise ValueError("pool inputs must use existing canonical IDs, such as Example0001")
    return inputs


def worker_homes(auth_root, jobs):
    """Validate metadata only; stores must come from separate native logins."""
    from . import bwrap

    if auth_root is None:
        raise ValueError("--auth-root is required; never share/copy a native login between slots")
    try:
        root = bwrap.canonical(auth_root)
        homes = [bwrap.canonical(root / f"worker-{slot}") for slot in range(1, jobs + 1)]
        identities = [bwrap.private_file(home / "auth.json") for home in homes]
        if len(set(homes)) != jobs or len(set(identities)) != jobs:
            raise ValueError("worker login stores must be distinct")
        return homes
    except (OSError, bwrap.SandboxError) as error:
        raise ValueError(f"invalid worker login store: {error}") from error


def save(path, value):
    save_bytes(path, (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + '\n').encode())


def save_bytes(path, data):
    path = Path(path)
    descriptor, temporary = tempfile.mkstemp(prefix='.record-', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)  # Atomic publication, fails if path exists.
    finally:
        os.unlink(temporary)


def read_bounded(path, maximum):
    descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW | os.O_CLOEXEC)
    with os.fdopen(descriptor, 'rb') as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1 or info.st_size > maximum:
            raise ValueError('invalid or oversized retained file')
        data = stream.read(maximum + 1)
        if len(data) > maximum:
            raise ValueError('oversized retained file')
        return data


def sha(data):
    return hashlib.sha256(data).hexdigest()
