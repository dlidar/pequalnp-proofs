#!/usr/bin/env bash
# Run with the project's pinned "lake env", from the directory with these sources.
set -eu
sources=$(pwd)
export LEAN_PATH="$sources:${LEAN_PATH:-}"
for module in Upper Core Logic $(seq -f 'Branch%g' 0 37) Lower; do
    lean -R "$sources" -o "$sources/$module.olean" "$sources/$module.lean"
done
