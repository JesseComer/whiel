#!/usr/bin/env python3
# Author: Fangzhu Shen
# Framework II adaptation based on her original agent setup.
"""Run on the target Linux host before selecting bwrap; no model/authentication call.

Uses only synthetic auth. Checks real kernel mounts/PID/FD isolation, request
Unix-socket connectivity, default TLS trust loading, the provider profile's own
credential policy (Codex in-place refresh, read-only Claude login state) and a
confined CLI --version startup without any credential mount.
Does not certify network isolation or a live authenticated consultation. External
services must not provide access to hidden campaign files. Live Codex login must
use file storage; other provider/login processes must stay idle during campaigns.
Select the route with --provider; the Claude route resolves its CLI from PATH or
--provider-cli and needs no pinned installation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import socket
import subprocess
import sys
import tempfile
import threading

REPO = Path(__file__).resolve().parent.parent
WRAPPER = REPO / "agent_houdini/bwrap.sh"

# Per-provider fixture layout. "marker" is an inert trailing argument: the Codex
# profile requires its file-auth selection to appear in the confined command,
# and the probe ignores the last argument in both routes.
PROVIDERS = {
    "codex": {"home_variable": "CODEX_HOME", "home_directory": ".codex",
              "auth_file": "auth.json", "credential_mode": "refresh",
              "marker": 'cli_auth_credentials_store="file"'},
    "claude": {"home_variable": "CLAUDE_CONFIG_DIR", "home_directory": ".claude",
               "auth_file": ".credentials.json", "credential_mode": "readonly",
               "marker": "whiel-preflight-inert-marker"},
}

# Executed by the target's Python inside the real bubblewrap namespace.
PROBE = r'''
import json,os,pathlib,socket,ssl,sys
mode,work,auth,fd,*denied=sys.argv[1:-1]
results={}
for index,path in enumerate(denied):
    try:
        with open(path,"rb") as stream: stream.read(1)
    except OSError: results["denied_"+str(index)]=True
    else: results["denied_"+str(index)]=False
try: os.fstat(int(fd))
except OSError: results["inherited_fd_closed"]=True
else: results["inherited_fd_closed"]=False
link=pathlib.Path(work)/"escape"
link.symlink_to(denied[0])
try: link.read_bytes()
except OSError: results["symlink_escape_denied"]=True
else: results["symlink_escape_denied"]=False
link.unlink()
with socket.socket(socket.AF_UNIX) as client:
    client.connect(str(pathlib.Path(work)/"bridge.sock"))
    client.sendall(b"fixture")
    results["request_socket"]=client.recv(16)==b"accepted"
if mode=="refresh":
    with open(auth,"w") as stream: stream.write("synthetic-refreshed")
    results["only_auth_in_codex_home"]=set(os.listdir(pathlib.Path(auth).parent))=={"auth.json"}
else:
    try:
        with open(auth,"a") as stream: stream.write("synthetic-write")
    except OSError: results["credentials_readonly"]=True
    else: results["credentials_readonly"]=False
    results["only_credentials_in_config_home"]=set(os.listdir(pathlib.Path(auth).parent))=={".credentials.json"}
(pathlib.Path(work)/"allowed").write_text("request-owned")
context=ssl.create_default_context()
results["default_ca_store_loaded"]=context.cert_store_stats().get("x509_ca",0)>0
try:
    with open("/etc/passwd","rb") as stream: stream.read(1)
except OSError: results["nonruntime_etc_hidden"]=True
else: results["nonruntime_etc_hidden"]=False
results["https_proxy_passthrough"]=os.environ.get("HTTPS_PROXY")=="http://127.0.0.1:9"
results["no_proxy_passthrough"]=os.environ.get("NO_PROXY")=="localhost,.invalid"
results["other_environment_removed"]=not any(
    name in os.environ for name in
    ("HTTP_PROXY","ALL_PROXY","SSL_CERT_FILE","OPENAI_API_KEY","ANTHROPIC_API_KEY",
     "ANTHROPIC_AUTH_TOKEN","CLAUDE_CODE_OAUTH_TOKEN","WHIEL_BWRAP_WORK")
)
print(json.dumps(results,sort_keys=True))
sys.exit(0 if all(results.values()) else 1)
'''


def cli_identity(provider, executable):
    """Provenance of the CLI exercised by the confined startup, never a pin.

    The Codex route reuses the optional pinned installer's verification. The
    Claude route accepts whatever `claude` the operator has installed.
    """
    if provider == "codex":
        return json.loads(subprocess.check_output(
            [sys.executable, str(REPO / "agent_houdini/setup_cli.py"), "--verify-only", "--json"],
            timeout=30))
    selected = executable or shutil.which("claude")
    if selected is None:
        raise RuntimeError("install the native Claude Code CLI on PATH, or pass --provider-cli")
    path = Path(selected).resolve(strict=True)
    if not path.is_file() or not os.access(path, os.X_OK):
        raise RuntimeError("the selected Claude CLI is not an executable file")
    return {"executable": str(path)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", choices=sorted(PROVIDERS), default="codex",
                        help="which confined provider profile to exercise")
    parser.add_argument("--provider-cli", help="explicit provider CLI path; otherwise PATH is resolved")
    parser.add_argument("--deny-path", action="append", default=[],
                        help="additional real certificate/proof file that must be invisible")
    args = parser.parse_args()
    if platform.system() != "Linux":
        print(json.dumps({"status": "unexecuted", "reason": "Linux target required; no fallback"}))
        return 125
    try:
        profile = PROVIDERS[args.provider]
        identity = cli_identity(args.provider, args.provider_cli)
        python = Path("/usr/bin/python3").resolve(strict=True)
        with tempfile.TemporaryDirectory(prefix="whiel-bwrap-preflight-") as temporary:
            root = Path(temporary).resolve()
            home = root / "home"
            provider_home = home / profile["home_directory"]
            provider_home.mkdir(parents=True, mode=0o700)
            auth = provider_home / profile["auth_file"]
            auth.write_text("synthetic-original")
            auth.chmod(0o600)
            work = root / "request"
            work.mkdir(mode=0o700)
            hidden = root / "certificate-sentinel"
            hidden.write_text("synthetic-private-certificate")
            previous = root / "previous-run"
            previous.write_text("synthetic-previous-run")
            (home / "private-other").write_text("synthetic-unmounted-home")
            real_proofs = sorted((REPO / "Benchmark").glob("*/Certificate/Valid.lean"))
            denied = [str(hidden), str(previous), str(home / "private-other"),
                      str(REPO / "TODO.md"),
                      f"/proc/{os.getpid()}/root{hidden}",
                      *map(str, real_proofs), *args.deny_path]
            env = {"PATH": "/usr/bin:/bin", "HOME": str(home),
                   profile["home_variable"]: str(provider_home),
                   "WHIEL_BWRAP_PROVIDER": args.provider,
                   "WHIEL_BWRAP_WORK": str(work), "WHIEL_BWRAP_RO": json.dumps([str(python)]),
                   "WHIEL_BWRAP_AUTH": "required", "WHIEL_BWRAP_TIMEOUT_SECS": "15",
                   "HTTPS_PROXY": "http://127.0.0.1:9", "NO_PROXY": "localhost,.invalid",
                   "HTTP_PROXY": "http://127.0.0.1:8", "ALL_PROXY": "socks5://127.0.0.1:7",
                   "SSL_CERT_FILE": "/synthetic/private-ca.pem",
                   "OPENAI_API_KEY": "synthetic-must-not-pass",
                   "ANTHROPIC_API_KEY": "synthetic-must-not-pass",
                   "ANTHROPIC_AUTH_TOKEN": "synthetic-must-not-pass",
                   "CLAUDE_CODE_OAUTH_TOKEN": "synthetic-must-not-pass"}
            listener = socket.socket(socket.AF_UNIX)
            listener.bind(str(work / "bridge.sock"))
            listener.listen(1)
            listener.settimeout(20)
            errors = []
            def serve():
                try:
                    connection, _ = listener.accept()
                    with connection:
                        connection.settimeout(2)
                        if connection.recv(16) != b"fixture":
                            raise RuntimeError("unexpected fixture request")
                        connection.sendall(b"accepted")
                except Exception as error:
                    errors.append(type(error).__name__)
            server = threading.Thread(target=serve)
            server.start()
            fd = os.open(hidden, os.O_RDONLY)  # Synthetic inherited-descriptor sentinel only.
            try:
                result = subprocess.run([str(WRAPPER), "--", str(python), "-c", PROBE,
                                         profile["credential_mode"], str(work), str(auth),
                                         str(fd), *denied, profile["marker"]], env=env,
                                        pass_fds=(fd,), capture_output=True, timeout=25)
            finally:
                os.close(fd)
                server.join(timeout=21)
                listener.close()
            if result.returncode or errors or server.is_alive():
                raise RuntimeError("kernel fixture failed: " + result.stderr.decode(errors="replace")[-2000:])
            outcomes = json.loads(result.stdout)
            content = auth.read_text()
            expected = "synthetic-refreshed" if profile["credential_mode"] == "refresh" else "synthetic-original"
            if content != expected or not all(outcomes.values()):
                raise RuntimeError("synthetic credential policy or visibility check failed")
            # No credential mount and no model call: exercise the confined CLI startup.
            env["WHIEL_BWRAP_AUTH"] = "none"
            env["WHIEL_BWRAP_RO"] = json.dumps(
                [identity["executable"], identity["catalog"]] if "catalog" in identity
                else [identity["executable"]])
            env.pop("HTTPS_PROXY")
            env.pop("NO_PROXY")
            version = subprocess.run([str(WRAPPER), "--", identity["executable"], "--version"],
                                     env=env, capture_output=True, timeout=25)
            if args.provider == "codex":
                confined = not version.returncode and version.stdout == b"codex-cli 0.148.0\n"
            else:
                # No version pin: the confined start itself is what is checked.
                confined = not version.returncode and version.stdout.strip() != b""
                identity = dict(identity,
                                version=version.stdout.decode(errors="replace").strip()[:256])
            if not confined:
                raise RuntimeError("confined CLI --version failed")
            print(json.dumps({"status": "passed", "platform": platform.platform(),
                              "architecture": platform.machine(), "identity": identity,
                              "provider": args.provider,
                              "credential_mount": profile["credential_mode"],
                              "wrapper_sha256": hashlib.sha256(WRAPPER.read_bytes()).hexdigest(),
                              "supervisor_sha256": hashlib.sha256(WRAPPER.with_suffix(".py").read_bytes()).hexdigest(),
                              "checks": outcomes,
                              "synthetic_refresh_persisted": profile["credential_mode"] == "refresh",
                              "confined_cli_version": True,
                              "live_authenticated_consultation": "unexecuted",
                              "network_isolation": "not provided; API network is shared"}, sort_keys=True))
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(json.dumps({"status": "failed", "reason": str(error)}), file=sys.stderr)
        return 125


if __name__ == "__main__":
    raise SystemExit(main())
