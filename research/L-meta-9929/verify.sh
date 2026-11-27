#!/usr/bin/env bash
# Run under the project's pinned lake environment. The C++ program supplies
# work estimates only; Lean checks every pruning step and final statement.
set -euo pipefail
cd "$(dirname "$0")"
root=$(pwd)
python3 subdivide.py
export LEAN_PATH="$root/parts:$root:${LEAN_PATH:-}"
for mod in Core Groups Coverage Cut; do
  lean -R "$root" -o "$mod.olean" "$mod.lean"
done
while IFS= read -r mod; do
  lean -R "$root" -o "parts/$mod.olean" "parts/$mod.lean"
done < parts/order
lean -R "$root" -o Lower.olean Lower.lean
