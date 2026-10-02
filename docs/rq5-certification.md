# RQ5 certification resource controls

The paper's first pass used a **300-second limit per certificate**, a
**10 GiB per-process RSS guard**, and **12 physical CPU cores per run**, with
**two runs concurrently on disjoint core sets**. Each run had 12 internal solver
workers and a 96 GiB aggregate process-tree RSS guard. Each Vampire job had a
300-second allowance within the certificate phase.

`campaign certify` supplies the certificate and solver clocks. CPU affinity,
concurrency and RSS supervision are host controls. The recipe below combines
Linux `taskset` and `ps` with the existing `watched_run` function in
[scripts/compare_certificate_builds.py](../scripts/compare_certificate_builds.py).
It imports only that general process watcher, not the script's reference-answer
experiment driver. No additional Python package is needed.

This recipe imposes those resource settings. It is not the paper's original
measurement supervisor: its whole-command timings and RSS samples have a
different measurement window, described below.

## Preparation

Complete the builds in [README.md](../README.md#linux-setup-and-builds) before
measurement. Avoid unrelated Lean builds: certificate bootstrap invokes the
repository's machine-wide Lean watchdog even when a prebuilt `--worker` is
supplied. The already-built prerequisites can then be reused.

Choose two **single-input**, accepted and uncertified search runs, such as child
runs produced by the [task pool](../agent_houdini/experiments/README.md).
Each verifier directory must contain exactly one `ExampleNNNN` directory and
one selected input in `summary.json`, with `Accepted.json` and its frozen answer.
There must be no existing `Certificate/`: `campaign certify` rechecks an existing
certificate instead of measuring fresh construction. Keep the original search
records unchanged; the recipe copies each verifier directory before certification.
Do not substitute benchmark reference answers for the accepted experimental
answers or override their recorded per-job solver profiles.

Inspect the Linux CPU topology:

```bash
lscpu -e=CPU,CORE,SOCKET,ONLINE
```

Choose two disjoint lists of 12 online CPUs, each representing 12 distinct
physical `(SOCKET, CORE)` pairs, with no physical core shared between lists.
The `0-11` and `12-23` masks below are illustrative: confirm or replace them for
the machine. Consecutive CPU IDs are not guaranteed to be distinct physical cores.

## Two concurrent certifications

Run from the repository root. Replace the two `REPLACE-WITH-...` paths with the
single-input verifier directories. Use a new output directory for every pair.
The assertions fail before launching if the copied inputs are not suitable.

```bash
python3 - <<'PYCODE'
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import os
import re
import shutil

from scripts.compare_certificate_builds import watched_run

repo = Path.cwd()
out = Path("artifacts/certification/rq5-pair-01")
sources = [
    (Path("artifacts/runs/REPLACE-WITH-FIRST-RUN/verifier"), "0-11"),
    (Path("artifacts/runs/REPLACE-WITH-SECOND-RUN/verifier"), "12-23"),
]
assert shutil.which("taskset") and shutil.which("ps")
assert not out.exists(), "choose a fresh output directory"

selected = []
for source, cpus in sources:
    cases = sorted(p for p in source.iterdir()
                   if p.is_dir() and re.fullmatch(r"Example[0-9]{4}", p.name))
    assert len(cases) == 1, "use a single-input search run"
    case = cases[0]
    summary = json.loads((source / "summary.json").read_text())
    assert summary["selected_inputs"] == [case.name]
    result = json.loads((case / "result.json").read_text())
    assert result["status"] in ("valid_uncertified", "invalid_uncertified")
    assert (case / "Accepted.json").is_file()
    assert sum((case / name).is_file()
               for name in ("Core.json", "Counterexample.json")) == 1
    assert not (case / "Certificate").exists()
    selected.append((source, cpus, case.name))

out.mkdir(parents=True)
attempts = []
for index, (source, cpus, identity) in enumerate(selected, 1):
    destination = out / f"run-{index}"
    shutil.copytree(source, destination)
    attempts.append((destination, cpus, identity))

env = dict(os.environ, WHIEL_CERTIFICATE_COMPILER="lake",
           WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS="0",
           WHIEL_CERTIFICATE_SOLVER_JOBS="12",
           LEAN_NUM_THREADS="12", LIMIT_KB="134217728")
env.pop("WHIEL_KEEP_CERTIFICATE_STAGE", None)

def certify(attempt):
    destination, cpus, identity = attempt
    command = [
        "taskset", "--cpu-list", cpus,
        "whiel_runner/target/release/whiel-symbolic", "campaign", "certify",
        "--run", str(destination), "--jobs", "1",
        "--certification-limit", "300", "--certificate-solver-limit", "300",
        "--retention", "all",
    ]
    receipt = watched_run(
        command, repo, env, destination / "supervisor.log",
        limit=float("inf"), memory_kb=96 * 1024 * 1024,
        process_memory_kb=10 * 1024 * 1024,
    )
    receipt.update(input=identity, cpu_list=cpus, command=command)
    (destination / "supervisor.json").write_text(
        json.dumps(receipt, indent=2, allow_nan=False) + "\n")
    return receipt

with ThreadPoolExecutor(max_workers=2) as executor:
    receipts = list(executor.map(certify, attempts))

print(json.dumps(receipts, indent=2))
if any(not r["cleanup_ok"] or r["inspection_error"] for r in receipts):
    raise SystemExit("inspection or cleanup failed; do not start another pair")
if any(r["outcome"] != "finished" for r in receipts):
    raise SystemExit("one or both attempts failed; inspect supervisor and certificate records")
PYCODE
```

`WHIEL_CERTIFICATE_COMPILER=lake` selects the Lake compiler path and
`WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS=0` leaves candidate attempts bounded
by the whole-certificate allowance rather than a separate candidate timer.
`WHIEL_CERTIFICATE_SOLVER_JOBS=12` controls solver jobs within one certificate;
`campaign certify --jobs 1` restricts each command to one input at a time.
The two Python workers run two independent commands concurrently. CPU affinity
is inherited by their children. `LEAN_NUM_THREADS=12` is supplied to the run;
bootstrap itself uses two Lean threads. `LIMIT_KB=134217728` gives the redundant
bootstrap watchdog a 128 GiB per-Lean threshold, while the process-owned watcher
enforces the tighter 10 GiB per-process and 96 GiB tree thresholds. RSS is summed
across processes, so shared pages may be counted more than once.

The watcher polls at roughly 0.2-second intervals and terminates the owned
process tree when it observes a memory excess. This is a sampled guard, not an
instantaneous OS limit. `prlimit --as` and `ulimit -v` instead restrict virtual
address space; Linux's `RLIMIT_RSS` does not enforce this RSS threshold. Do not
substitute those controls while claiming the same memory policy.

The watcher receives an infinite *whole-command* time allowance because the
CLI enforces the 300-second *per-certificate* limit after bootstrap. Wrapping
the entire command in `timeout 300` would charge setup against the certificate
budget. The independent 300-second Vampire allowance is also required: changing
a solver-visible time limit can change its search behavior.

## Outcomes and measurements

The watcher saves `supervisor.json` and `supervisor.log` beside each copied
campaign. A memory kill or inspection failure can interrupt the campaign before
it updates `result.json` or `summary.json`; in that case the supervisor's failure
is authoritative. Its `finished` status means only command exit 0. Validate the
published certificate, exact original theorem and expected axioms using
[AUDIT.md](../AUDIT.md). Stop after any inspection or cleanup failure; do not
launch another pair until the owned processes and cause have been checked.
This example dispatches only the two selected attempts and makes no retries.

The watcher's `elapsed_seconds` covers bootstrap, certification and joined
cleanup. Its `peak_process_rss_kb` and `peak_tree_rss_kb` are sampled during the
whole-command polling loop: they include bootstrap and can include samples
collected after the certificate deadline; cleanup does not add peak samples.
They are not the original supervisor's strictly predeadline certificate peaks.
Use the certificate's own phase timing for its budgeted execution and label
wrapper wall time and peaks separately. A full reproduction of the paper's
measurement window additionally needs sampling keyed to each certificate's
start/deadline, with cleanup and later lifetime samples kept separate.

For extended retries, preserve the first-pass records and use new output copies.
The retry settings are a 3,600-second certificate limit, a 31,536,000-second
solver allowance within it, no separate per-process RSS limit, and a 128 GiB
aggregate tree guard. Keep retry outcomes and costs separate from the initial
300-second pass; the solver-visible allowances differ.
