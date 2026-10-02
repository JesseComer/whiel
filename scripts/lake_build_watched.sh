#!/bin/bash
# `lake build` with a per-process memory watchdog: any `lean` worker whose RSS
# exceeds the limit (default 4 GB) is killed, and the build reports failure.
# Usage: scripts/lake_build_watched.sh [lake build args...]
#   LIMIT_KB (env, default 4194304) and LEAN_NUM_THREADS (env, default 2).
# Run from any worktree: the build happens in the repo containing this script.
set -u
cd "$(dirname "$0")/.." || exit 1
LIMIT_KB="${LIMIT_KB:-4194304}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
lake build "$@" &
LP=$!
KILLED=0
while kill -0 "$LP" 2>/dev/null; do
  for p in $(pgrep -x lean); do
    r=$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' ')
    if [ -n "$r" ] && [ "$r" -gt "$LIMIT_KB" ]; then
      echo "WATCHDOG KILL pid=$p rss=${r}KB (limit ${LIMIT_KB} KB)" >&2
      kill -9 "$p"; KILLED=1
    fi
  done
  sleep 2
done
wait "$LP"; RC=$?
[ "$KILLED" = 1 ] && [ "$RC" = 0 ] && RC=137
echo "build exit $RC"
exit "$RC"
