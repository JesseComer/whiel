#!/bin/sh
# Optional Linux confinement. Failure never falls back to local execution.
set -eu
exec /usr/bin/python3 "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)/bwrap.py" "$@"
