# Author: Fangzhu Shen
"""Offline rendering of exactly what the agent reads for a recorded push.

`python3 -m agent_houdini render-prompt PATH` prints the prompt C would build
for one consultation, without a provider, a verifier or a network. PATH is a
recorded observation JSON document, a `{observation, response_example}` pair,
or a directory holding one; a directory is searched for the first such file.
The golden-prompt test renders the recorded Example0001 first consultation
this way and compares the result byte for byte, so a prompt change is a diff.
"""

from pathlib import Path
import sys

from .json_wire import JsonWireError, decode, encode
from .prompt import render_prompt


MAX_DOCUMENT_BYTES = 8 * 1024 * 1024
MAX_SEARCHED_FILES = 4096
# A recorded observation carries no response example unless the record paired
# them. Rendering offline still needs one document of the exact shape, so a
# placeholder is shown, marked by its zero digests. C never reconstructs a
# real binding: a placeholder is for reading, never for submission.
PLACEHOLDER_EXAMPLE = {
    "binding": {name: "0" * 64 for name in (
        "consultation_digest", "request_digest", "run_digest", "scope_digest",
        "state_snapshot_digest", "task_digest", "validation_manifest_digest")},
    "clauses": [], "dropped": [], "kind": "candidate_clauses", "schema_version": 4,
}


class RenderError(ValueError):
    """The named path holds no recorded observation this tool can render."""


def is_observation(value) -> bool:
    return (isinstance(value, dict) and isinstance(value.get("feedback"), dict)
            and "correction" in value)


def consultation(document):
    """The observation and its response example, from either recorded shape."""
    if is_observation(document):
        return document, PLACEHOLDER_EXAMPLE
    if isinstance(document, dict) and is_observation(document.get("observation")):
        example = document.get("response_example")
        return document["observation"], example if isinstance(example, dict) else PLACEHOLDER_EXAMPLE
    return None


def read_document(path: Path):
    try:
        if path.stat().st_size > MAX_DOCUMENT_BYTES:
            return None
        return consultation(decode(path.read_bytes(), maximum=MAX_DOCUMENT_BYTES))
    except (JsonWireError, OSError):
        return None


def find_consultation(path: Path):
    """One recorded consultation from a JSON file or a campaign directory."""
    path = Path(path)
    if path.is_file():
        found = read_document(path)
        if found is None:
            raise RenderError(f"{path} holds no recorded observation")
        return found, path
    if not path.is_dir():
        raise RenderError(f"{path} is not a file or a directory")
    for index, candidate in enumerate(sorted(path.rglob("*.json"))):
        if index >= MAX_SEARCHED_FILES:
            break
        if candidate.is_file() and not candidate.is_symlink():
            found = read_document(candidate)
            if found is not None:
                return found, candidate
    raise RenderError(f"no recorded observation under {path}")


def render(path, *, budget_bytes=None, first_consultation=None):
    (observation, example), source = find_consultation(path)
    prompt = render_prompt(observation, encode(example),
                           first_consultation=first_consultation,
                           budget_bytes=budget_bytes)
    return prompt, source


def main(argv, *, out=None, notes=None) -> int:
    """`out` and `notes` let the golden test drive this without touching stdio."""
    notes = sys.stderr if notes is None else notes
    if len(argv) != 1 or argv[0] in ("-h", "--help"):
        print("Usage: python3 -m agent_houdini render-prompt PATH\n"
              "PATH is a recorded observation JSON file or a campaign directory.",
              file=notes)
        return 0 if argv[:1] in ([], ["-h"], ["--help"]) else 2
    prompt, source = render(argv[0])
    print(f"agent_houdini render-prompt: {source} ({len(prompt)} bytes)", file=notes)
    stream = sys.stdout.buffer if out is None else out
    stream.write(prompt)
    stream.flush()
    return 0
