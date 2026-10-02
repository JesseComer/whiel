#!/usr/bin/env python3
# Author: Fangzhu Shen
# Framework II adaptation based on her original agent setup.
"""Optional Linux process wrapper; no credential content is opened or copied.

Usage: agent_houdini/bwrap.sh -- /absolute/provider-cli <args>
WHIEL_BWRAP_PROVIDER: profile name selecting the confined home/credential layout.
WHIEL_BWRAP_WORK: fresh request-only directory (including its bridge socket).
WHIEL_BWRAP_RO: JSON array of exact CLI/catalog/bridge readonly regular files.
WHIEL_BWRAP_TIMEOUT_SECS: positive remaining provider allowance, including lock wait.
WHIEL_BWRAP_AUTH: required (default), or none for unauthenticated fixtures.
HOME and the provider's configuration directory retain their usual paths; only
that provider's own login files are mounted, never the surrounding home.
External provider/login processes must not concurrently use the same auth source.
Networking is shared for the model API; this is not a network isolation claim.
Only selected CA trust and DNS configuration under /etc is mounted read-only;
the complete host /etc is not exposed.
HTTPS_PROXY and NO_PROXY are selectively inherited when present.
"""
from __future__ import annotations

import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import stat
import subprocess
import sys
import time
from collections import namedtuple
from collections.abc import Mapping, Sequence


# Public host runtime material only.  Keep private TLS directories such as
# /etc/pki/tls/private out of the namespace.  RHEL's files under
# /etc/pki/tls/certs are absolute symlinks into the extracted trust store, so
# both the public link directory and its public targets must be present.
SYSTEM_READONLY_PATHS = (
    "/usr/lib", "/usr/lib64", "/lib", "/lib64",
    "/etc/ssl/certs", "/etc/pki/tls/certs",
    "/etc/pki/ca-trust/extracted/pem",
    "/etc/pki/ca-trust/extracted/openssl",
    "/etc/resolv.conf", "/etc/hosts", "/etc/nsswitch.conf",
)

# RHEL's conventional OpenSSL cafile is an absolute symlink to this public
# extracted bundle.  Bind the reviewed public source to the conventional name
# instead of following an unconstrained host alias.
SYSTEM_READONLY_BINDINGS = (
    ("/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem",
     "/etc/pki/tls/cert.pem"),
)

# Inherit only these host variables.  In particular, proxy URLs remain in the
# environment rather than bwrap's argv, where embedded credentials could be
# exposed through the process command line.
PASSTHROUGH_ENVIRONMENT = ("HTTPS_PROXY", "NO_PROXY")

# Per-provider confined layout. The wrapper, not the provider adapter, decides
# the home layout, which login files are mounted and how, and the complete
# child environment, so no adapter argument can widen the namespace.
#   home_variable/home_directory: the CLI's configuration directory
#   auth_files: login files that must exist, be private, and be mounted
#   auth_bind: --bind keeps a CLI's own in-place refresh; --ro-bind forbids it
#   state_files: optional noncredential login state, mounted read-only if present
#   data_resources: readonly resource names allowed to be nonexecutable
#   required_arguments: alternative arguments, one of which must select file auth
#   environment: additional confined environment entries
PROVIDER_PROFILES = {
    "codex": {
        "home_variable": "CODEX_HOME",
        "home_directory": ".codex",
        "auth_files": ("auth.json",),
        "auth_bind": "--bind",
        "state_files": (),
        "data_resources": ("models.json",),
        "required_arguments": ('cli_auth_credentials_store="file"',
                               "cli_auth_credentials_store=file"),
        "environment": (("CODEX_INTERNAL_APP_SERVER_REMOTE_CONTROL_DISABLED", "1"),),
    },
    # Claude Code keeps its Linux login in its configuration directory and has
    # no file-auth selection argument. Its credentials are mounted read-only:
    # the confined CLI can read the existing login but cannot rewrite it, and
    # no login byte is copied into the request workspace or a log.
    "claude": {
        "home_variable": "CLAUDE_CONFIG_DIR",
        "home_directory": ".claude",
        "auth_files": (".credentials.json",),
        "auth_bind": "--ro-bind",
        "state_files": (".claude.json", "settings.json"),
        "data_resources": (),
        "required_arguments": (),
        "environment": (
            ("CLAUDE_CODE_DISABLE_ATTACHMENTS", "1"),
            ("CLAUDE_CODE_DISABLE_AUTO_MEMORY", "1"),
            ("CLAUDE_CODE_DISABLE_CLAUDE_MDS", "1"),
            ("CLAUDE_CODE_DISABLE_GIT_INSTRUCTIONS", "1"),
            ("CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC", "1"),
            ("CLAUDE_CODE_DISABLE_OFFICIAL_MARKETPLACE_AUTOINSTALL", "1"),
            ("ENABLE_CLAUDEAI_MCP_SERVERS", "false"),
            ("ENABLE_TOOL_SEARCH", "false"),
        ),
    },
}

Configuration = namedtuple(
    "Configuration",
    "provider profile work readonly home provider_home auth_mode timeout persist_usage")


class SandboxError(Exception):
    pass


def require(value, message):
    if not value:
        raise SandboxError(message)


def canonical(raw):
    path = Path(raw)
    require(path.is_absolute() and path.resolve() == path, "path must be absolute and free of symlinks")
    return path


def python_relay_resources(interpreter: Path, relay: Path) -> tuple[Path, Path]:
    """Exact files supported by the existing Linux system-library mounts.

    Resolving the system Python alias is intentional; custom and virtualenv
    interpreters may need libraries outside those mounts and are not supported
    by this optional wrapper. Local execution has no such restriction.
    """
    require(Path(interpreter).is_absolute(), "Python relay interpreter must be absolute")
    python = Path(interpreter).resolve(strict=True)
    require(python.parent == Path("/usr/bin")
            and re.fullmatch(r"python3(?:\.[0-9]+)?", python.name) is not None,
            "bubblewrap relay requires a system /usr/bin/python3 interpreter; no local fallback")
    script = canonical(relay)
    for path in (python, script):
        info = path.lstat()
        require(stat.S_ISREG(info.st_mode) and info.st_mode & 0o111
                and not info.st_mode & 0o022,
                "Python relay resources must be exact readonly executable files")
    return python, script


def wrap_native_command(
    argv: Sequence[str], environment: Mapping[str, str], work: Path,
    readonly_resources: Sequence[Path], timeout_seconds: float, *,
    auth_mode: str = "required", provider: str = "codex", persist_usage: bool = False,
) -> tuple[tuple[str, ...], dict[str, str]]:
    """Prepare the C wrapper without starting a process or opening credentials.

    The native builder supplies its exact executable/catalog and the MCP
    bridge's exact runtime files. The wrapper repeats these checks immediately
    before launch. Existing mount and environment policy remains authoritative.
    """
    require(platform.system() == "Linux", "bubblewrap mode requires Linux; no local fallback")
    require(provider in PROVIDER_PROFILES, "unsupported provider profile; no local fallback")
    require(bool(argv) and all(isinstance(arg, str) and "\0" not in arg for arg in argv),
            "native command must contain string arguments without NUL")
    require(all(isinstance(key, str) and isinstance(value, str)
                and "\0" not in key and "=" not in key and "\0" not in value
                for key, value in environment.items()), "invalid native environment")
    env = dict(environment)
    env.update({"WHIEL_BWRAP_PROVIDER": provider, "WHIEL_BWRAP_WORK": str(work),
                "WHIEL_BWRAP_RO": json.dumps([str(path) for path in readonly_resources]),
                "WHIEL_BWRAP_TIMEOUT_SECS": str(timeout_seconds),
                "WHIEL_BWRAP_AUTH": auth_mode})
    env["WHIEL_BWRAP_PERSIST_USAGE"] = "1" if persist_usage else "0"
    settings(env, argv)
    wrapper = canonical(Path(__file__).resolve().with_name("bwrap.sh"))
    require(wrapper.is_file() and os.access(wrapper, os.X_OK), "C bubblewrap wrapper is missing")
    return (str(wrapper), "--", *argv), env


def private_file(path):
    """Metadata only. Never open auth content, including for hashing."""
    path = canonical(path)
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and info.st_uid == os.getuid()
            and info.st_nlink == 1 and info.st_mode & 0o777 == 0o600,
            "auth must be an owned, single regular file with mode 0600")
    for parent in path.parents:
        entry = parent.lstat()
        require(stat.S_ISDIR(entry.st_mode) and entry.st_uid in (0, os.getuid()), "unsafe auth ancestor")
        require(not entry.st_mode & 0o022 or
                (entry.st_uid == 0 and entry.st_mode & stat.S_ISVTX), "writable auth ancestor")
    return info.st_dev, info.st_ino, info.st_uid, info.st_mode, info.st_nlink


def contains(parent, child):
    return parent == child or parent in child.parents


def child_environment(env):
    """Build the complete, deliberately minimal environment inherited by bwrap."""
    result = {"PATH": "/usr/bin:/bin"}
    for name in PASSTHROUGH_ENVIRONMENT:
        if name in env:
            result[name] = env[name]
    return result


def settings(env, command):
    require(command and Path(command[0]).is_absolute(), "command must use an absolute executable")
    provider = env.get("WHIEL_BWRAP_PROVIDER", "codex")
    require(provider in PROVIDER_PROFILES, "unsupported provider profile")
    profile = PROVIDER_PROFILES[provider]
    work = canonical(env["WHIEL_BWRAP_WORK"])
    require(work.is_dir() and work.stat().st_uid == os.getuid()
            and not work.stat().st_mode & 0o077, "request directory must be owned and private")
    for entry in work.rglob("*"):
        info = entry.lstat()
        require(not stat.S_ISLNK(info.st_mode) and info.st_uid == os.getuid()
                and (stat.S_ISDIR(info.st_mode) or stat.S_ISSOCK(info.st_mode)
                     or (stat.S_ISREG(info.st_mode) and info.st_nlink == 1)),
                "request work contains a linked or foreign resource")
        require(entry.name.lower() not in {".git", "benchmark", "certificate", "certificates",
                                            "core", "proof", "proofs", "lean-toolchain"}
                and entry.suffix != ".lean", "request work contains repository or proof material")
    readonly = json.loads(env["WHIEL_BWRAP_RO"])
    require(isinstance(readonly, list) and readonly and all(isinstance(x, str) for x in readonly),
            "readonly resources must be a nonempty JSON file list")
    readonly = [canonical(x) for x in readonly]
    require(len(set(readonly)) == len(readonly), "duplicate readonly resource")
    for path in readonly:
        info = path.lstat()
        require(stat.S_ISREG(info.st_mode) and not info.st_mode & 0o022,
                "readonly resources must be regular files without group/world write access")
        require(info.st_mode & 0o111 or path.name in profile["data_resources"],
                "readonly resources must be runtime executables or a declared data resource")
        require(not contains(work, path), "readonly resource overlaps request work")
        require(not any(part.lower() in {"benchmark", "certificate", "certificates", "core", "proof", "proofs", "results_summary"}
                        for part in path.parts), "proof or certificate resource is forbidden")
    require(canonical(command[0]) in readonly, "executable must be an exact readonly resource")
    home = canonical(env["HOME"])
    provider_home = canonical(env.get(profile["home_variable"],
                                      str(home / profile["home_directory"])))
    require(home.is_dir() and provider_home != home and not contains(provider_home, home),
            "the provider configuration directory must be distinct from and not contain HOME")
    require(not contains(work, provider_home) and not contains(provider_home, work),
            "request and provider configuration directory overlap")
    auth_mode = env.get("WHIEL_BWRAP_AUTH", "required")
    require(auth_mode in ("required", "none"), "invalid auth mode")
    if auth_mode == "required" and profile["required_arguments"]:
        require(any(arg in profile["required_arguments"] for arg in command),
                "native file auth backend must be explicitly configured")
    require(not any(contains(provider_home, path) for path in readonly),
            "the provider configuration directory is not a protocol resource")
    timeout = float(env["WHIEL_BWRAP_TIMEOUT_SECS"])
    require(math.isfinite(timeout) and timeout > 0, "provider timeout must be positive and finite")
    persist_usage = env.get("WHIEL_BWRAP_PERSIST_USAGE", "0")
    require(persist_usage in ("0", "1"), "invalid usage persistence mode")
    if persist_usage == "1":
        sessions = work / "usage-sessions"
        require(provider == "codex" and sessions.is_dir()
                and not any(sessions.iterdir()), "usage sessions must be fresh and Codex-only")
    return Configuration(provider, profile, work, readonly, home, provider_home,
                         auth_mode, timeout, persist_usage == "1")


def auth_resources(config):
    """Exact login files this profile mounts. Their content is never opened."""
    return tuple(config.provider_home / name for name in config.profile["auth_files"])


def mount_command(bwrap, config, command):
    profile = config.profile
    work, home = config.work, config.home
    args = [bwrap, "--unshare-all", "--share-net", "--new-session", "--die-with-parent",
            "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
            "--tmpfs", "/run", "--tmpfs", str(home), "--perms", "0700",
            "--dir", str(config.provider_home)]
    # System libraries and TLS/DNS files only; no host /etc, /run or home bind.
    for raw in SYSTEM_READONLY_PATHS:
        path = Path(raw)
        if path.exists():
            args += ["--ro-bind", str(path.resolve()), raw]
    for source_raw, target in SYSTEM_READONLY_BINDINGS:
        source = Path(source_raw)
        if source.is_file() and not source.is_symlink():
            args += ["--ro-bind", str(source), target]
    for path in config.readonly:
        args += ["--ro-bind", str(path), str(path)]
    args += ["--bind", str(work), str(work)]
    if config.persist_usage:
        # Mount only this request's empty output directory, never the host's
        # session history or any additional credential/configuration files.
        args += ["--bind", str(work / "usage-sessions"), str(config.provider_home / "sessions")]
    if config.auth_mode == "required":
        for auth in auth_resources(config):
            args += [profile["auth_bind"], str(auth), str(auth)]
    # Optional noncredential login state, read-only and only when it exists.
    for name in profile["state_files"]:
        state = config.provider_home / name
        if state.is_file() and not state.is_symlink():
            args += ["--ro-bind", str(state), str(state)]
    args += ["--chdir", str(work), "--setenv", "HOME", str(home),
             "--setenv", profile["home_variable"], str(config.provider_home),
             "--setenv", "PATH", "/usr/bin:/bin",
             "--setenv", "TMPDIR", "/tmp", "--setenv", "LANG", "C.UTF-8"]
    for name, value in profile["environment"]:
        args += ["--setenv", name, value]
    args += ["--", *command]
    return args


def acquire_auth_lock(auth, deadline, cancelled):
    # Only this noncredential lock is opened. Stable path identity, not auth bytes.
    directory = Path("/tmp").resolve() / f"whiel-agent-auth-{os.getuid()}"
    try:
        directory.mkdir(mode=0o700)
    except FileExistsError:
        pass
    directory = canonical(directory)
    info = directory.lstat()
    require(stat.S_ISDIR(info.st_mode) and info.st_uid == os.getuid()
            and info.st_mode & 0o777 == 0o700, "unsafe auth lock directory")
    name = hashlib.sha256(os.fsencode(auth)).hexdigest() + ".lock"
    fd = os.open(directory / name, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
    try:
        info = os.fstat(fd)
        require(stat.S_ISREG(info.st_mode) and info.st_uid == os.getuid()
                and info.st_nlink == 1 and info.st_mode & 0o777 == 0o600, "unsafe auth lock")
        while True:
            require(not cancelled(), "cancelled while awaiting native auth lock")
            require(time.monotonic() < deadline, "timed out awaiting native auth lock")
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return fd
            except BlockingIOError:
                time.sleep(min(0.05, max(0, deadline - time.monotonic())))
    except BaseException:
        os.close(fd)
        raise


def supervise(args, deadline, cancelled, environment):
    child = subprocess.Popen(args, close_fds=True, start_new_session=True,
                             env=environment)
    try:
        while child.poll() is None:
            if cancelled() or time.monotonic() >= deadline:
                child.terminate()
                try:
                    child.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.wait()
                return 130 if cancelled() else 124
            time.sleep(0.02)
        return child.returncode
    finally:
        if child.poll() is None:
            child.kill()
        child.wait()
        # bwrap's private PID namespace dies with its init; no host PID /proc view.


def main(argv=None):
    command = list(sys.argv[1:] if argv is None else argv)
    if command and command[0] == "--":
        command.pop(0)
    lock = None
    cancelled = [False]
    previous = {}
    try:
        require(platform.system() == "Linux", "bubblewrap mode requires Linux; no local fallback")
        bwrap = next((p for p in ("/usr/bin/bwrap", "/bin/bwrap") if Path(p).is_file()), None)
        require(bwrap is not None, "bubblewrap is missing; install bwrap explicitly, no local fallback")
        config = settings(os.environ, command)
        deadline = time.monotonic() + config.timeout
        for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            previous[signum] = signal.signal(signum, lambda *_: cancelled.__setitem__(0, True))
        auth = auth_resources(config)
        identity = None
        if config.auth_mode == "required":
            lock = acquire_auth_lock(auth[0], deadline, lambda: cancelled[0])
            identity = tuple(private_file(path) for path in auth)
        args = mount_command(bwrap, config, command)
        environment = child_environment(os.environ)
        if identity is not None:
            require(tuple(private_file(path) for path in auth) == identity,
                    "auth source substituted before startup")
        require(not cancelled[0] and time.monotonic() < deadline, "cancelled or timed out before startup")
        result = supervise(args, deadline, lambda: cancelled[0], environment)
        if identity is not None:
            require(tuple(private_file(path) for path in auth) == identity,
                    "auth source identity changed; use normal CLI login")
        return result
    except (SandboxError, OSError, KeyError, ValueError) as error:
        print(f"agent_houdini_bwrap: {error}", file=sys.stderr)
        return 125
    finally:
        if lock is not None:
            os.close(lock)
        for signum, handler in previous.items():
            signal.signal(signum, handler)


if __name__ == "__main__":
    raise SystemExit(main())
