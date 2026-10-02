# Providers, authentication and setup

The native CLI owns authentication. WHIEL does not embed a provider account,
API key, login token or organization ID. The Python harness manages native
setup, auth metadata and the MCP relay; the Rust verifier does not inspect them. Each collaborator uses their own native login;
changing provider/model does not change Lean or certificate authority.

## Toolchain prerequisites

Use a supported Unix host: the development gates run on macOS arm64; the
maintained Codex package lock also covers Linux x86_64/aarch64. Windows is not
supported by this process adapter. Install Git, Python **3.10 or newer**,
Rust/Cargo supporting edition 2024, elan, and C/C++ build tools/CMake/Make
for the pinned solver. The provider Python package uses only the standard
library and does not require Node.js.
Lean is pinned by [`lean-toolchain`](../lean-toolchain); executable roles and
hashes live in [`toolchain.lock.json`](../toolchain.lock.json).

On Debian/Ubuntu, typical base packages are `build-essential`, `cmake`, `git`,
`curl`, `python3` and `pkg-config`; optional isolation also needs `bubblewrap`.
Install Rust and elan through their maintained installers, then use the
[quickstart build](campaign-quickstart.md). Toolchain validation, not this package
list, decides whether a native host is ready. Do not reuse macOS executable
hashes on Linux. The Linux pin procedure below is required before strict runs.

### Python command resolution

The harness requires Python 3.10 features, including `dataclass(slots=True)`.
The repository's scripts and subprocesses invoke `python3`, so installing a
newer interpreter is not sufficient unless that command resolves to it:

```bash
python3 -c 'import sys; print(sys.version); assert sys.version_info >= (3, 10), "Python 3.10+ required"'
```

The default `python3` on the tested RHEL 9 host was Python 3.9. With a system
Python 3.11 installed and available as `python3.11`, the following checkout-local
shim selects it without replacing the operating system's interpreter. Run this
from the repository root, then retain the `PATH` setting in every shell that
launches a campaign:

```bash
mkdir -p artifacts/python-bin
ln -s "$(command -v python3.11)" artifacts/python-bin/python3
export PATH="$PWD/artifacts/python-bin:$PATH"
python3 --version
```

Create the symlink once; on later shells only the `PATH` export is needed.
The shim points to the native interpreter; it does not create a virtualenv.

### Mathlib cache on Linux

The [quickstart build](campaign-quickstart.md#build-once) fetches Mathlib's
precompiled cache before building the Lean worker. Without it, a fresh clone
compiles the required Mathlib modules from source. Two failures were encountered
while setting up a fresh RHEL 9 host:

- **CA bundle lookup:** the cache tool may download its own curl when the
  system curl is too old. If transfers fail with an OpenSSL `STORE routines`
  / `unregistered scheme` error, point both curl trust variables at the
  distribution's existing CA bundle. This command locates the `ca-bundle.crt`
  supplied by RHEL's `ca-certificates` package:

  ```bash
  whiel_ca_bundle="$(rpm -ql ca-certificates | awk '/\/certs\/ca-bundle\.crt$/ {print; exit}')"
  test -r "$whiel_ca_bundle" &&
    export SSL_CERT_FILE="$whiel_ca_bundle" CURL_CA_BUNDLE="$whiel_ca_bundle"
  ```

  If no readable file is found, inspect `rpm -ql ca-certificates` and select
  the host's installed CA bundle before retrying; do not disable TLS checks.

- **Open-file limit during unpacking:** a many-core host can exhaust its
  soft descriptor limit while decompressing the cache. Raise the soft limit
  to the permitted hard limit and restrict the cache command to at most eight
  CPUs from the current process's allowed CPU set:

  ```bash
  ulimit -n "$(ulimit -Hn)"
  whiel_cache_cpus="$(python3 -c 'import os; print(",".join(map(str, sorted(os.sched_getaffinity(0))[:8])))')"
  taskset -c "$whiel_cache_cpus" env LEAN_NUM_THREADS=1 \
    scripts/watchdog.sh 4194304 lake exe cache get
  ```

  Downloaded archives are retained, so retrying can reuse them for unpacking.
  This CPU restriction applies to setup only, not to subsequent experiments.

## Codex setup and native login

Install the Codex CLI yourself and log in with it. The harness runs whichever
`codex` is on `PATH`, or the one named by `--provider-cli /absolute/path/to/codex`:

```bash
codex -c 'cli_auth_credentials_store="file"' login
```

An optional pinned installation is still available for the Linux confinement
route below. It downloads a pinned Codex release and checked model catalog under
`artifacts/provider-cli/` and does not log in:

```bash
python3 agent_houdini/setup_cli.py
python3 agent_houdini/setup_cli.py --verify-only --json
```

The C-owned pin for that optional installer is
[`agent_houdini/toolchain/cli-lock.json`](../agent_houdini/toolchain/cli-lock.json).
Point `--provider-cli` at the installed executable to use it for a campaign; the
runtime itself requires no pinned install, version or model catalog.

C disables every Codex feature it can name through the CLI's own `--disable`
switches and `-c` settings, and gives each turn a private scratch directory as
its working directory. Codex 0.145.0 exposes no configuration switch that
removes its apply-patch (file editing) tool: which form of that tool the model
sees comes from the provider's model catalog, which C no longer pins. Under
`--isolation bwrap` on Linux the wrapper still confines writes to the request
workspace; under local isolation an edit can reach any path the invoking user
can write, so run local Codex campaigns from an account that has nothing else
to lose, or use the Linux confinement route below.

For an SSH/headless host, use native `login --device-auth`. The native CLI also
supports `login --with-api-key`, reading the key from stdin. If you deliberately
choose API billing, supply it through your secret manager or an already-protected
environment variable, never as a campaign argument or literal shell-history value:

```bash
printenv OPENAI_API_KEY | codex -c 'cli_auth_credentials_store="file"' login --with-api-key
```

This is native Codex login, not a WHIEL key option. A paid API key is not required
when an eligible native ChatGPT login is used; account/model access and billing
belong to the provider. See [OpenAI authentication documentation](https://developers.openai.com/codex/auth/).
The launcher pins file-backed native auth under the user's `CODEX_HOME` (default
`HOME/.codex`) and preserves native refresh. Avoid competing logins/campaigns
against the same native auth source during a run. `--model` is required, accepts
any string the provider CLI understands and is passed through verbatim; the
optional `--reasoning-effort` behaves the same way. Pass native choices before the
`--` separator; see the [CLI reference](cli-reference.md#agenthoudini-launcher).

## Claude setup and native login

Install **native Claude Code** using
[Anthropic's setup instructions](https://code.claude.com/docs/en/setup), and log
in with `claude auth login` in your own terminal. WHIEL does not install Claude
or use `--bare`, which would disable the native login route. Any installed
version is accepted: the adapter runs a single best-effort `claude --version`
probe, bounded at 15 seconds, and records the reported string as provenance
only. A CLI that does not answer the probe is recorded as an unknown version and
still runs. Use `--provider-cli /absolute/path/to/claude` before the launcher
separator when needed; otherwise `PATH` is resolved once.

The adapter expects an ordinary native login on a local host and does not bypass
organization policy; a managed installation may refuse the options it sets.
Native Claude supports
several [authentication methods](https://code.claude.com/docs/en/authentication),
but this adapter intentionally does not forward `ANTHROPIC_API_KEY`,
`ANTHROPIC_AUTH_TOKEN`, `CLAUDE_CODE_OAUTH_TOKEN` or custom API endpoint variables.
An exported key alone is therefore **not** a supported WHIEL Claude setup.
There is no direct key, gateway, Bedrock, Vertex or Foundry integration.
Use the supported CLI-owned login; authenticated Claude execution has not been
verified here. `CLAUDE_CONFIG_DIR` (or `HOME/.claude`) selects native configuration.

The runtime disables native file/exec tools, user/project customization and
implicit MCP sources, then checks the startup event: the whiel MCP server must be
connected, the exposed tool list must equal the selected WHIEL tools, the reported
model must equal the requested model, the permission mode must be the restricted
one, and no plugin or MCP error may be present. The reported CLI version is never
compared.
Only selected WHIEL tools and exact submission reach the controller. No built-in
file tool can be enabled with arbitrary extra provider arguments.

## The thinking allowance is advisory

`--agent-thinking-tokens N` is a C agent allowance passed to the CLI as its
per-turn thinking cap, so a turn cannot spend its whole consultation budget
thinking and never reach a tool call. It is a cap the CLI applies to the model's
own thinking budget, not a hard bound on what the CLI afterwards reports: in a
recorded campaign two of twenty-two requests reported per-turn thinking
estimates above a 4000-token allowance. Treat it as advisory pressure toward
acting. The bound that actually ends a turn is C's deadline — B's remaining
request budget — and B's cancellation remains authoritative over both.

## Keeping a real run diagnosable

C's event log always names why a consultation failed, including which side
closed the MCP exchange and what the provider CLI had last reported. Add
`--agent-retention all` to also keep, per consultation, the rendered prompt, the
CLI's complete stream-JSON stdout and stderr, every MCP request and reply, and
every submission payload with B's verdict, under
`<agent-log-dir>/<ID>/request-<n>/`. Sizes are capped,
truncation is marked, and credential-looking lines are withheld on write.
Read a finished run with `python3 -m agent_houdini show-run <agent-log-dir>`.
See `agent_houdini/README.md` for the file layout.

## Optional Linux isolation (bubblewrap)

Local mode works without bubblewrap. `--isolation bwrap` is an explicit Linux
option of C's launcher and is available for both providers. The host must permit
user/PID namespaces. For every provider the wrapper mounts the fresh request
workspace, the exact selected CLI executable, canonical system Python and
executable C relay, system runtime dependencies, and selected public CA trust and
DNS lookup files under `/etc`. The complete host `/etc` is not mounted, and the
home directory itself is a private tmpfs: only the named login files below are
visible. Networking to the model is available. If present, exactly `HTTPS_PROXY`
and `NO_PROXY` are inherited from the host; other provider keys — including
`OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `ANTHROPIC_AUTH_TOKEN` and
`CLAUDE_CODE_OAUTH_TOKEN` — and all other host environment variables are removed
before startup. Proxy values stay out of the command line. Proxy settings are
trusted host configuration and must not be populated from benchmark input.

The wrapper, not the provider adapter, owns the confined layout. It selects one
of two profiles:

| | Codex | Claude |
|---|---|---|
| configuration directory | `CODEX_HOME` (default `HOME/.codex`) | `CLAUDE_CONFIG_DIR` (default `HOME/.claude`) |
| credential file | `auth.json`, read-write | `.credentials.json`, **read-only** |
| optional login state | none | `.claude.json`, `settings.json`, read-only when present |
| added confined variables | `CODEX_INTERNAL_APP_SERVER_REMOTE_CONTROL_DISABLED` | the adapter's Claude Code feature-disable variables |

Both profiles apply the same private-path and symlink rejections: the credential
file must be an owned, single, non-symlinked regular file with mode 0600, no
ancestor may be group/world writable, readonly resources must be exact
non-symlinked regular files outside the request workspace, and no proof or
certificate material may be mounted.

A Linux operator running the Claude route needs, before the campaign:

- `bubblewrap` installed, and user/PID namespaces permitted.
- An ordinary native login performed outside the sandbox, leaving
  `$CLAUDE_CONFIG_DIR/.credentials.json` (default `~/.claude/.credentials.json`)
  owned by the campaign user with mode 0600.
- The `claude` executable **outside** the configuration directory — for example
  `~/.local/bin/claude`. The configuration directory is never a protocol
  resource, so an executable installed inside `~/.claude` cannot be mounted.
- A currently valid login. The confined CLI mounts its credentials read-only, so
  it can read the existing login but cannot rewrite or refresh it, and no login
  byte is copied into the request workspace or a log. Refresh the login with a
  normal unconfined `claude` run when it expires; other provider or login
  processes must stay idle during a campaign.

```bash
python3 agent_houdini/preflight.py                     # Codex profile
python3 agent_houdini/preflight.py --provider claude    # Claude profile
python3 -m agent_houdini campaign run \
  --verifier "$PWD/whiel_runner/target/release/whiel-symbolic" --isolation bwrap \
  --provider claude --model <model> --provider-cli /absolute/path/to/claude \
  -- --repo "$PWD" --input Example0001
```

The preflight uses synthetic credentials and checks TLS trust loading, that
unrelated `/etc` files remain hidden, exact proxy-variable passthrough, file
visibility, socket and descriptor isolation, the profile's credential policy
(Codex in-place refresh; a Claude credential mount that refuses writes), and a
confined CLI `--version` startup with no credential mount at all. The Codex route
exercises the pinned installer's CLI; the Claude route exercises whichever
`claude` is on `PATH` or named by `--provider-cli`, and records its reported
version as provenance without comparing it to a pin. Neither route makes a model
call or proves real account refresh. Record a separate bounded native test on the
target host before a campaign. Explicit isolation failure never silently falls
back. The preserved wrapper also rejects unsupported custom/virtualenv
interpreters instead of mounting their runtime trees.

The checked-in unit tests for both profiles are pure argument-construction tests
and run anywhere. They make no claim about real
Linux namespace, mount, TLS or credential behavior: that is established only by
running the preflight and a bounded native test on the target Linux host.

### Vampire build environments and local pins

`toolchain.lock.json` pins executable SHA-256 values for `Linux-x86_64` and
`Darwin-arm64`. The recorded build environments are:

| Platform | Compiler | CMake |
| --- | --- | --- |
| Linux x86_64 | GCC 11.5.0, Red Hat 11.5.0-14 | 3.31.8 |
| macOS arm64 | Apple clang 17.0.0, clang-1700.6.4.2 | 4.3.4 |

The compiler and CMake descriptions are provenance. The build script enforces
the source and ordered patches; the toolchain check verifies the locked binaries,
patch files and dependency identities. It does not merely compare compiler names.
Build and check the recorded identity with:

```bash
mkdir -p artifacts
python3 scripts/build_leancheck_vampire.py --jobs 2 --json \
  > artifacts/vampire-build.json
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 python3 scripts/check_toolchain.py
```

The build script places the solver in `toolchain/build/`. It captures subprocess
output and writes its JSON receipt at completion, so a quiet redirected log is
not itself evidence of a failed build.

A different compiler environment can produce a different binary digest from
the same pinned source. To record a local build for such an environment:

```bash
python3 scripts/build_leancheck_vampire.py --jobs 2 --bootstrap --force --json \
  > artifacts/vampire-bootstrap.json
```

`--force` replaces the generated solver checkout, including one left by a strict
build whose digest did not match. Run it only when no job uses that checkout or
solver. `--bootstrap` does **not** edit the lock. Its exit status and `ok: true` do not
mean strict checks passed: bootstrap allows a proposed binary identity. Inspect
the receipt's individual `checks`, `source_commit`, `applied_commits`,
`applied_commit`, `expected_applied_commit`, `version`, `platform`, `compiler`
and `sha256`. The source and ordered patch commits must still match the lock;
version checks must pass. A compiler-specific repin should account only for
the expected `binary_sha256` mismatch, not unrelated failures.

After that review, record the receipt's digest in
`roles.leancheck_vampire.sha256[platform]` in `toolchain.lock.json`, using the
receipt's platform key (`Linux-x86_64` or `Darwin-arm64`). Update the corresponding
`roles.leancheck_vampire.platforms[platform]` compiler and build-environment
metadata to describe the local build. Keep the source, patch series, Lean, Lake,
CaDiCaL and other pins unchanged. Retain the build receipt with the experiment
records. Recheck the updated local identity:

```bash
LEAN_NUM_THREADS=1 scripts/watchdog.sh 4194304 python3 scripts/check_toolchain.py
```

A successfully checked local pin allows runs with that build, but it is not the
paper's original binary identity. Subsequent certificate receipts record a
different `pinned_leancheck_vampire_sha256`; preserve that distinction when
comparing or sharing results. The local pin does not establish that a compiler
change leaves solver performance unchanged.
