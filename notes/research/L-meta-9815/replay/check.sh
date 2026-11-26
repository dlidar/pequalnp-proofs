#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
project=$(cd "$src/../../../../lean" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cp "$src"/../*.lean "$src"/*.lean "$scratch"
python3 "$src/generate.py" "$scratch"
cd "$project"
lake build PEqualNP.Defs
lake env bash -euc '
  cd "$1"
  export LEAN_PATH="$PWD:${LEAN_PATH:-}"
  for m in FormulaMass CachedBase Upper OptimalBase UsefulAll Invert Prune Cert{0..81} CacheLower Strong{0..11} Classification; do
    lean -o "$m.olean" "$m.lean"
  done
  cat > EndAudit.lean <<EOF
import Classification
import Invert
#print axioms PEqualNP.Research.Cached9815.exact_per_cache
#print axioms PEqualNP.Research.Cached9815.best_cache_size
#print axioms PEqualNP.Research.Cached9815.invert_one_bound
#print axioms PEqualNP.Research.Cached9815.ordinary_optimum
EOF
  lean EndAudit.lean
' bash "$scratch"
