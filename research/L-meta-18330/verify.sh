#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
cd "$root/lean"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.36.0
lake build PEqualNP.Defs
project_path=$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')
lean_bin=$(lake env which lean)
cd "$here"
export LEAN_PATH="$here:$project_path"
for f in FormulaMass CachedBase Rep0 Rep1 Rep2 Rep3 Rep4 Rep5 Transport Upper Reference Exact Erase Audit; do
    "$lean_bin" -o "$f.olean" "$f.lean"
done
python3 verify_weights.py
