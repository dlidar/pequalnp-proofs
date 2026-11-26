#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
project=$(cd "$src/../../../lean" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cp "$src"/*.lean "$scratch"
cd "$project"
lake build PEqualNP.Outside.L_meta_1018
lake env bash -euc '
  cd "$1"
  export LEAN_PATH="$PWD:${LEAN_PATH:-}"
  for module in FormulaMass IndependentTriple18872 TriangleCertificate SingleInverter FormulaApplication TriangleOwners FactoredCost SharpDesign TreeBound Audit; do
    lean -o "$module.olean" "$module.lean"
  done
' bash "$scratch"
