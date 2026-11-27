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
g++ -O3 -std=c++17 small-decoder.cpp -o smalldec
python3 pinning.py
python3 recheck-packs.py
python3 checkweights.py
python3 rawcerts.py
python3 splitcert.py
python3 chunkcert.py
mapfile -t powerset_modules < chunk-order
mods=(FormulaMass Bridge Context Leaves Convert Three Triple Realize Reference Graph Restrict Witness Signed FormulaTree Cert{0..2} Cert3Base Cert3Test{0..5} "${powerset_modules[@]}" Cert3Test8 Cert{3..7} Result)
for m in "${mods[@]}"; do "$lean_bin" -o "$m.olean" "$m.lean"; done
for mod in "${mods[@]}"; do python3 audit.py "$mod"; "$lean_bin" Audit.lean; done
