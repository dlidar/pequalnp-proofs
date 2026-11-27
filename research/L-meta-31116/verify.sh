#!/bin/bash
set -euo pipefail
# Run in a separate checkout's lean directory using its pinned lake env.
cd "$(dirname "$0")"
dir=$PWD
: "${LEAN_PROJECT:?Set LEAN_PROJECT to the absolute path to the pinned project's lean directory}"
(cd "$LEAN_PROJECT" && lake env lean --version)
export LEAN_PATH="$dir:$(cd "$LEAN_PROJECT" && lake env printenv LEAN_PATH)"
compiler=$(cd "$LEAN_PROJECT" && lake env which lean)
for m in Reference Universal Boundary Merge Features Audit; do "$compiler" -o "$m.olean" "$m.lean"; done
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
