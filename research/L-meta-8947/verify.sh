#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
cd "$root/lean"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.36.0
lake build PEqualNP.Defs PEqualNP.Outside.L_meta_5351
project_path=$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')
lean_bin=$(lake env which lean)
cd "$here"
export LEAN_PATH="$here:$project_path"
for module in Density Amplify Consequence Residual Matching Disjoint Audit; do
    "$lean_bin" -o "$module.olean" "$module.lean"
done
