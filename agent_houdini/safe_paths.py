# Author: Fangzhu Shen
"""Recording a filesystem path without this machine's own layout in it.

A run directory is made to be read later, copied to another machine and
exported to a collaborator who never had this checkout at this location. A
path under the checkout being studied is still meaningful there and is
recorded relative to it; a path outside the checkout says nothing portable on
a different machine and is better lost than kept as this machine's home
directory or user name. An executable outside the checkout is recorded by its
own file name, which still says what ran without saying where it lives;
anything else outside the checkout becomes a fixed placeholder.
"""

from pathlib import Path


OUTSIDE_REPOSITORY = "<outside-repository>"


def safe_path(path, repo, *, executable=False):
    """`path`'s safe recorded form: relative to `repo`, or the fallback.

    `path` may be `None`, a `str` or a `Path`; `repo` is the checkout every
    in-repo path is recorded relative to. Never raises on a path that does
    not exist: only its components are resolved, never its content read.
    """
    if path is None:
        return None
    try:
        relative = Path(path).resolve().relative_to(Path(repo).resolve())
    except (OSError, ValueError):
        return Path(str(path)).name if executable else OUTSIDE_REPOSITORY
    return relative.as_posix() or "."


def safe_argv(argv, repo, *, executables=()):
    """One command line, each absolute path token made safe.

    `executables` names the exact absolute-path values (as given in `argv`)
    that are the interpreter or binary actually run, so one of them, if
    outside `repo`, keeps its file name instead of becoming the placeholder.
    Every other token is returned unchanged.
    """
    executables = set(executables)
    safe = []
    for token in argv:
        if isinstance(token, str) and token.startswith("/"):
            safe.append(safe_path(token, repo, executable=token in executables))
        else:
            safe.append(token)
    return safe


def safe_environment(environment, repo):
    """One environment mapping, each absolute-looking value made safe."""
    safe = {}
    for key, value in environment.items():
        if isinstance(value, str) and value.startswith("/"):
            safe[key] = safe_path(value, repo)
        else:
            safe[key] = value
    return safe
