#!/usr/bin/env bash
# Run from this directory inside the project's pinned lake environment.
set -eu
d=$(pwd)
python3 subdivide.py
export LEAN_PATH="$d/parts:$d:${LEAN_PATH:-}"
lean -R "$d/.." -o "$d/../Formulas.olean" "$d/../Formulas.lean"
for mod in Core Groups Coverage Cut; do
 lean -R "$d" -o "$d/$mod.olean" "$d/$mod.lean"
done
while read -r mod; do
 lean -R "$d/parts" -o "$d/parts/$mod.olean" "$d/parts/$mod.lean"
done < "$d/parts/order"
lean -R "$d" -o "$d/Lower.olean" "$d/Lower.lean"
