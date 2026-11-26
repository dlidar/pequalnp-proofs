#!/usr/bin/env bash
set -euo pipefail
# Run from the project's pinned Lean environment with the project imports built.
cd "$(dirname "$0")"
export LEAN_PATH="$PWD:${LEAN_PATH:-}"
for unit in Upper Core Logic; do lean -o "$unit.olean" "$unit.lean"; done
for ((i=0; i<48; i++)); do lean -o "Branch$i.olean" "Branch$i.lean"; done
lean -o Lower.olean Lower.lean
