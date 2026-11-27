#!/usr/bin/env bash
# From this directory inside the pinned project's Lean environment.
set -eu
export LEAN_PATH="$PWD:$PWD/parts:$LEAN_PATH"
for name in Core Groups Coverage Cut; do lean -o "$name.olean" "$name.lean"; done
python3 subdivide.py
(cd parts; while read -r name; do lean -o "$name.olean" "$name.lean"; done <order)
lean -o Lower.olean Lower.lean
