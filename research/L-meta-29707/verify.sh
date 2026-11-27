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
for mod in FormulaMass Bridge Context Leaves Convert Reference Graph Three Audit; do
  "$lean_bin" -o "$mod.olean" "$mod.lean"
done
g++ -std=c++17 -O3 profiles.cpp -o profiles
./profiles mono.bin
g++ -std=c++17 -O3 checkprofiles.cpp -o checkprofiles
./checkprofiles mono.bin
python3 checksmall.py
g++ -std=c++17 -O3 cache.cpp -o cache
./cache > cache-replay.txt
cmp cache-results.txt cache-replay.txt
python3 rect.py
python3 cube.py
python3 - <<'PY'
from upper import witnesses
from collections import Counter
import json
g=witnesses()['gates']
assert len(g)==14 and json.load(open('upper.json'))['gates']==list(map(list,g))
uses=Counter(k for _,i,j in g for k in (i,j))
assert all(uses[i]==1 for i in range(8,21)) and uses[21]==0
print('14-gate formula; every non-output gate used once; all 256 inputs checked')
PY
