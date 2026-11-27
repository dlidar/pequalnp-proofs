#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
project=$(cd -- "${1:?pass the pinned upstream lean project directory}" && pwd)
cd "$project"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.36.0
project_path=$(lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))')
lean_bin=$(lake env which lean)
cd "$here"
export LEAN_PATH="$here:$project_path"
for mod in CoreClass Census Orbits FormulaMass Core0 Core1 Core2 Core3 Audit; do
  "$lean_bin" -o "$mod.olean" "$mod.lean"
done
python3 "$here/verify.py"
