# Author: Fangzhu Shen
"""Distinct public C campaign-launcher and generic-endpoint modes."""
from pathlib import Path
import sys

# B invokes this C file from its private working directory. Bootstrap only this
# package; the proposer never imports verifier source or private executables.
if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from agent_houdini.launcher import main


if __name__ == "__main__":
    raise SystemExit(main())
