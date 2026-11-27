#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
cd "${1:?pass the pinned project lean directory}"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.36.0
project_path=$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')
lean_bin=$(lake env which lean)
cd "$here"
export LEAN_PATH="$here:$project_path"
for s in profiles checkprofiles cache rectbound cube5; do g++ -O3 -std=c++17 "$s.cpp" -o "$s"; done
./profiles mono.bin
./checkprofiles mono.bin
./cache
./rectbound > covers.txt
python3 budget.py
./cube5
python3 checkweights.py
python3 rawcerts.py
mods=(FormulaMass Bridge Context Leaves Convert Three Triple Realize Reference Graph Signed FormulaTree Cert{0..7} Result)
for m in "${mods[@]}"; do "$lean_bin" -o "$m.olean" "$m.lean"; done
python3 audit.py "${mods[@]}"
"$lean_bin" Audit.lean
