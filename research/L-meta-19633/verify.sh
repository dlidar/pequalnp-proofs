#!/usr/bin/env bash
# From this source directory, run inside the project's pinned lake environment.
set -eu
d=$(pwd)
export LEAN_PATH="$d:${LEAN_PATH:-}"
for mod in Upper Core Groups Coverage $(seq -f 'Batch%g' 0 44) Lower; do
    lean -R "$d" -o "$d/$mod.olean" "$d/$mod.lean"
done
