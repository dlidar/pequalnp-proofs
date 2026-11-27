#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
cd "${1:?pass the pinned project lean directory}"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.36.0
project_path=$(lake env python3 -c 'import os;print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')
lean_bin=$(lake env which lean)
cd "$here"
export LEAN_PATH="$here:$here/../L-meta-29313:$project_path"
for f in FormulaMass Bridge Context Leaves Convert Three Triple; do (cd ../L-meta-29313 && "$lean_bin" -o "$f.olean" "$f.lean"); done
for s in profiles checkprofiles one-share-check; do g++ -O3 -std=c++17 "$s.cpp" -o "$s"; done
./profiles mono.bin
./checkprofiles mono.bin
./one-share-check
python3 checkweights.py
python3 cutwidth.py
python3 cutcert.py
python3 check-cuts.py
python3 gen-balanced.py
for f in Reference Graph FormulaTree Witness Inverter Cut Four Both Examples; do "$lean_bin" -o "$f.olean" "$f.lean"; done
for f in Cut[0-9]*.lean; do "$lean_bin" -o "${f%.lean}.olean" "$f"; done

python3 gen-total.py
"$lean_bin" -o Total.olean Total.lean
python3 balanced.py
g++ -O3 -std=c++17 five-dp.cpp -o five-dp
./five-dp > five-costs
python3 decoder-cost.py
g++ -O3 -std=c++17 decoder-circuits.cpp -o decoder-circuits
./decoder-circuits > decoder-tables
python3 circuit-prices.py
g++ -O3 -std=c++17 encoders.cpp -o encoders
./encoders 7 < encoder-queries.txt > encoder-prices.txt
g++ -O3 -std=c++17 encoder-witness.cpp -o encoder-witness
python3 assemble-cuts.py
g++ -O3 -std=c++17 two-cache.cpp -o two-cache
./two-cache
