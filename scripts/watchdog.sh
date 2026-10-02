#!/bin/bash
# Run a command, killing it if its RSS (including children) exceeds 4 GB.
# Usage: watchdog.sh <limit_kb> <command...>
LIMIT_KB="$1"; shift
"$@" &
PID=$!
while kill -0 "$PID" 2>/dev/null; do
  # Sum RSS (KB) of the process and every descendant.
  TOTAL=$(ps -Ao pid,ppid,rss | awk -v root="$PID" '
    { rss[$1]=$3; ppid[$1]=$2; pids[NR]=$1 }
    END {
      total=0
      for (i=1; i<=NR; i++) {
        p=pids[i]; q=p; depth=0
        while (q != 0 && q != "" && depth < 64) {
          if (q == root) { total += rss[p]; break }
          q = ppid[q]; depth++
        }
      }
      print total
    }')
  if [ -n "$TOTAL" ] && [ "$TOTAL" -gt "$LIMIT_KB" ]; then
    echo "WATCHDOG: killing $PID at ${TOTAL} KB RSS (limit ${LIMIT_KB} KB)" >&2
    pkill -P "$PID" 2>/dev/null
    kill -9 "$PID" 2>/dev/null
    wait "$PID" 2>/dev/null
    exit 137
  fi
  sleep 2
done
wait "$PID"
exit $?
