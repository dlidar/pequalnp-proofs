#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
cd "${1:?pass pinned upstream lean project directory}"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.36.0
project_path=$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')
lean_bin=$(lake env which lean)
cd "$here"
export LEAN_PATH="$here:$project_path"
for mod in Reference Repair Necessity Boundary AllTraces Approx OneError IsEssential Ports Shared Twelve Canalyzing Audit; do "$lean_bin" -o "$mod.olean" "$mod.lean"; done
for src in profiles checkprofiles census rectbound two; do g++ -O3 -std=c++17 "$src.cpp" -o "$src"; done
./profiles table.bin
./checkprofiles table.bin
python3 catalog.py
./census > census.txt
python3 - <<'PY'
import json
h=json.load(open('catalog.json'))['leaf_cost_histograms']
assert [[r.get(str(k),0) for k in range(16)] for r in h]==[list(map(int,l.split())) for l in open('census.txt')]
PY
./rectbound > covers.txt
python3 budget.py
./rectbound partial > partial-covers.txt
python3 partial.py
./two
test ! -e repair-witness.txt
