#!/usr/bin/env bash
set -euo pipefail
# Run from a shell using the project's pinned lake environment.
cd "$(dirname "$0")"
mkdir -p split
cp Core.lean Logic.lean Lower.lean Upper.lean Branch*.lean Prune.lean split/
python3 refine.py 85000
python3 pack.py
cd split
export LEAN_PATH="$PWD:${LEAN_PATH:-}"
for unit in Upper Core Logic Prune; do lean -o "$unit.olean" "$unit.lean"; done
while IFS= read -r unit; do lean -o "$unit.olean" "$unit.lean"; done < packed-order
