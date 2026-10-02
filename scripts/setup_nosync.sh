#!/bin/bash
# setup_nosync.sh — keep generated trees out of cloud sync.
#
# iCloud Drive never syncs a file or folder whose name ends in `.nosync`.
# For a working copy that lives inside an iCloud-synced folder (Desktop,
# Documents, or iCloud Drive), this script replaces each generated tree
# with a `<name>.nosync` directory behind a path-preserving symlink, so
# build output and run artifacts never enter the sync set while every
# tool keeps using the original paths. Sync engines pay per file, not per
# byte; build trees and artifact stores produce exactly the flood of
# small files that overwhelms them.
#
# Idempotent: safe to run any number of times. Outside an iCloud-synced
# location it exits without changing anything (override with --force).

set -euo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd -P)"

case "${1:-}" in
  --force) forced=1 ;;
  "") forced=0 ;;
  *) echo "usage: $0 [--force]" >&2; exit 2 ;;
esac

if [ "$forced" -eq 0 ]; then
  case "$repo" in
    "$HOME/Desktop/"* | "$HOME/Documents/"* | "$HOME/Library/Mobile Documents/"*) ;;
    *)
      echo "setup_nosync: $repo is not inside an iCloud-synced folder;" \
        "nothing to do (--force to override)"
      exit 0
      ;;
  esac
fi

link_nosync() {
  local parent="$1" name="$2"
  local dir="$parent/$name" twin="$parent/$name.nosync"
  if [ -L "$dir" ]; then
    echo "setup_nosync: $name already linked"
    return
  fi
  if [ -e "$dir" ] && [ -e "$twin" ]; then
    echo "setup_nosync: both $dir and $twin exist; merge or remove one, then re-run" >&2
    exit 1
  fi
  if [ -e "$dir" ]; then
    mv "$dir" "$twin"
  else
    mkdir -p "$twin"
  fi
  ln -s "$name.nosync" "$dir"
  echo "setup_nosync: $name -> $name.nosync"
}

link_nosync "$repo" artifacts
link_nosync "$repo" .lake
link_nosync "$repo" .venv
link_nosync "$repo" results_summary
link_nosync "$repo/whiel_runner" target
link_nosync "$repo/toolchain" build
