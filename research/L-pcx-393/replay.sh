#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
cd "${1:?pass the project lean directory}"
lake build +PEqualNP.Outside.L_pcx_375
export LEAN_PATH="$src:$(lake env printenv LEAN_PATH)"
for mod in Order Dictionary Prefix Paths InventoryBound Size Audit; do
  lake env lean --version >/dev/null
  (cd "$src" && lean -o "$mod.olean" "$mod.lean")
done
