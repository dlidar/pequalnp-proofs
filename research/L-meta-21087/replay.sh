#!/usr/bin/env bash
# Start in this research directory with the pinned project's Lean imports available.
set -eu
research_dir=$(pwd)
export LEAN_PATH="$research_dir/split:$LEAN_PATH"
lean -R "$research_dir" -o Upper.olean Upper.lean
python3 refine.py 18000
cd split
for mod in Core Logic Prune $(seq -f 'Branch%g' 0 10); do
 lean -o "$mod.olean" "$mod.lean"
done
while read -r mod; do lean -o "$mod.olean" "$mod.lean"; done < order
