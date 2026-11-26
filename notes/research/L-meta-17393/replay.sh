#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$src" rev-parse --show-toplevel)
stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
cp "$src"/*.lean "$src/audit.py" "$src/modules.txt" "$stage/"
cd "$repo/lean"
lake build PEqualNP.Defs
lake env bash -euc '
  cd "$1"
  export LEAN_PATH="$PWD:$LEAN_PATH"
  for m in $(cat modules.txt); do lean -o "$m.olean" "$m.lean"; done
  python3 audit.py > Audit.lean
  lean Audit.lean > audit.log
  python3 audit.py audit.log
' bash "$stage"
