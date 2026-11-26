#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(git -C "$source_dir" rev-parse --show-toplevel)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cp "$source_dir"/*.lean "$source_dir/audit.py" "$scratch"
cd "$repo_root/lean"
lake build PEqualNP.Defs PEqualNP.MetaComplexity.Helpers.LowMergeWires PEqualNP.MetaComplexity.Helpers.EdgeUpper
export LEAN_PATH="$scratch:$(lake env printenv LEAN_PATH)"
lean_bin=$(lake env which lean)
cd "$scratch"
for name in LeafCount StarPools Pool Charge ExactPool Application Example Girth Ordinary; do
  "$lean_bin" -o "$name.olean" "$name.lean"
done
python3 audit.py > Audit.lean
"$lean_bin" Audit.lean > audit.log
python3 audit.py audit.log
