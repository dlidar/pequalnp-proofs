#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
project=$(cd "$src/../../../lean" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cp "$src"/*.lean "$src/generate.py" "$src/pairs.json" "$scratch"
cd "$scratch"
python3 generate.py
cd "$project"
lake build PEqualNP.Defs
lake env bash -euc '
  cd "$1"
  export LEAN_PATH="$PWD:${LEAN_PATH:-}"
  for module in Signed16092 Samples Upper16092 Frontier; do
    lean -o "$module.olean" "$module.lean"
  done
  for module in Root{0..64} RootProof ExactNegation Optima; do
    lean -o "$module.olean" "$module.lean"
  done
' bash "$scratch"
