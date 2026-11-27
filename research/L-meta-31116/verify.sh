#!/bin/bash
set -euo pipefail
# Run in a separate checkout's lean directory using its pinned lake env.
cd "$(dirname "$0")"
dir=$PWD
: "${LEAN_PROJECT:?Set LEAN_PROJECT to the absolute path to the pinned project's lean directory}"
(cd "$LEAN_PROJECT" && lake env lean --version)
export LEAN_PATH="$dir:$(cd "$LEAN_PROJECT" && lake env printenv LEAN_PATH)"
compiler=$(cd "$LEAN_PROJECT" && lake env which lean)
for m in Reference Universal Boundary Merge Features Alternation Late Audit; do "$compiler" -o "$m.olean" "$m.lean"; done
g++ -std=c++17 -O3 profiles.cpp -o profiles
./profiles mono.bin
g++ -std=c++17 -O3 verify-prices.cpp -o verify-prices
./verify-prices
python3 upper.py
python3 census.py
python3 extremes.py
g++ -std=c++17 -O3 prefixes.cpp -o prefixes
./prefixes
python3 decoder.py
python3 tasks.py
g++ -std=c++20 -O3 frontier.cpp -o frontier
g++ -std=c++20 -O3 fast.cpp -o fast

python3 controls.py
g++ -std=c++20 -O3 deep.cpp -o deep
g++ -std=c++20 -O3 deep-fast.cpp -o deep-fast
g++ -std=c++20 -O3 slow-split.cpp -o slow-split
g++ -std=c++20 -O3 deep-direct.cpp -o deep-direct
# The following are the larger exact checks.
# ./fast full.task 13
# ./slow-split full.task 13
# for d in 1 2 3 4 5 6; do ./deep-fast "$d"; done
# ./deep-direct 5
