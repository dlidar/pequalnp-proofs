#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
project=$(cd "$src/../../../lean" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
python3 "$src/verify.py"
cp "$src"/*.lean "$scratch"
cd "$project"
lake build PEqualNP.Defs
lake env bash -euc '
  cd "$1"
  export LEAN_PATH="$PWD:${LEAN_PATH:-}"
  for module in FormulaMass CachedBase Upper Invert StartAudit; do
    lean -o "$module.olean" "$module.lean"
  done
' bash "$scratch"
